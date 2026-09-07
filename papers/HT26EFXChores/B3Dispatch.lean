import HT26EFXChores.HighRatioGapFilling
import HT26EFXChores.M34Extension

/-!
# Source-to-model dispatch for the high-ratio `b = 3` branch

This module starts the outer dispatcher for Case B.4 of He--Tao.  It first
closes the residual-exception split in B.4.1(a): after the two intersecting
edge chores have gap-filled the unique short prefix bundle, the source treats
nonexceptional residues, exceptional pairs avoiding the short agent, and
exceptional pairs containing that agent separately.

Source: `EFXadditivechores.tex`, lines 3006--3110.
-/

namespace HT26EFXChores

open AppliedModelingLib.FairDivision

/-- Every exceptional M₂ residue has two distinct, ordered auxiliary
endpoints.  This exposes the pair that the source calls the exceptional pair;
the order is immaterial at this structural stage but is needed by the two
controlled-combination kernels. -/
theorem exists_ordered_exceptional_endpoints
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (hexceptional : IsM2Exceptional cost chores) :
    ∃ first second : Fin 4, first ≠ second ∧
      IsM2ExceptionalWithEndpoints cost chores first second := by
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hshape⟩
  obtain ⟨first, second, hne, hauxiliaryEq⟩ := Finset.card_eq_two.mp hauxiliary
  refine ⟨first, second, hne, ?_⟩
  refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_, hshape⟩
  · simp [hauxiliaryEq]
  · simp [hauxiliaryEq]

/-- The ordered exceptional-endpoint presentation is symmetric. -/
theorem IsM2ExceptionalWithEndpoints.swap
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (first second : Fin 4)
    (hexceptional : IsM2ExceptionalWithEndpoints cost chores first second) :
    IsM2ExceptionalWithEndpoints cost chores second first := by
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hfirst, hsecond, hshape⟩
  exact ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, hsecond, hfirst,
    hshape⟩

/-- A canonical bundle is entirely own-small whenever the agent has at least
as many own-small chores in the pool as her assigned quota.  This is the
bridge from the source's heavy-agent argument to the all-small long-bundle
premises in Cases B.4.2(b) and B.4.3(b). -/
theorem canonical_bundle_all_small_of_quota_le_ownSmall
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (quota : Fin 4 → ℕ) (allocation : Allocation (Fin 4) Item)
    (agent : Fin 4)
    (hcanonical : IsCanonicalSmallChoreAllocation cost chores quota allocation)
    (hownSmall : quota agent ≤ (ownSmallChoreSet cost chores agent).card) :
    ∀ chore ∈ allocation agent, IsSmallChore cost agent chore := by
  classical
  have hcanonicalOwn : (ownSmallChoreSet cost (allocation agent) agent).card =
      quota agent := by
    rw [hcanonical.2 agent |>.2, Nat.min_eq_left hownSmall]
  have hownEq : ownSmallChoreSet cost (allocation agent) agent = allocation agent := by
    apply Finset.eq_of_subset_of_card_le
    · intro chore hchore
      exact (Finset.mem_filter.mp hchore).1
    · rw [hcanonicalOwn, hcanonical.2 agent |>.1]
  intro chore hchore
  have hsmallOwn : chore ∈ ownSmallChoreSet cost (allocation agent) agent := by
    rw [hownEq]
    exact hchore
  exact (Finset.mem_filter.mp hsmallOwn).2

/-- If no super-canonical prefix can make a specified agent short in the
`b=3` case, that agent is heavy in the precise source sense of owning at
least `2a+1` M₀₁-small chores.  Otherwise the short-light canonical lemma
would construct the forbidden prefix. -/
theorem heavy_ownSmall_of_no_supercanonical_short
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (chores : Finset Item) (a : ℕ) (agent : Fin 4)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hchores : chores.card = 4 * a + 3)
    (hsmall : ∀ chore ∈ chores, IsSmallForAtMostOne cost chore)
    (hnoSuper : ¬ ∃ allocation,
      IsCanonicalSmallChoreAllocation cost chores (canonicalQuota a (Finset.univ \ {agent}))
        allocation ∧
      ∀ own comparison,
        canonicalQuota a (Finset.univ \ {agent}) own = a →
        canonicalQuota a (Finset.univ \ {agent}) comparison = a + 1 →
        additiveChoreCost cost own (allocation own) ≤
          additiveChoreCost cost own (allocation comparison) - r) :
    2 * a + 1 ≤ (ownSmallChoreSet cost chores agent).card := by
  by_contra hnotHeavy
  have hlight : (ownSmallChoreSet cost chores agent).card ≤ 2 * a := by omega
  obtain ⟨allocation, hcanonical, hsuper⟩ :=
    existsSuperCanonicalOfShortLight Item r cost chores {agent}
      (Finset.univ \ {agent}) a 3 (by linarith) hcost (by omega) hsmall hchores rfl
      (by simp) (by
        intro other hother
        have hotherEq : other = agent := by simpa using hother
        subst other
        exact hlight)
  exact hnoSuper ⟨allocation, hcanonical, hsuper⟩

/-- In the B.4.1(b) prefix switch, failure of super-canonicity with agent `0`
short certifies that agent `0` owns at least `a + 1` M₀₁-small chores.  If she
owned at most `a`, canonicity would put every one of her small chores in her
short bundle and every other prefix bundle would be entirely large for her,
which is already super-canonical. -/
theorem ownSmallCard_succ_le_of_not_supercanonical_zero_short
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hnotSuper : ¬ ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r) :
    a + 1 ≤ (ownSmallChoreSet cost prefixChores 0).card := by
  classical
  by_contra hnotEnough
  have hsmallBound : (ownSmallChoreSet cost prefixChores 0).card ≤ a := by omega
  have hcanonicalOwn :
      (ownSmallChoreSet cost (prefixAllocation 0) 0).card =
        (ownSmallChoreSet cost prefixChores 0).card := by
    rw [hcanonical.2 0 |>.2, hquota0, Nat.min_eq_right hsmallBound]
  have hprefixOwnSubset : prefixAllocation 0 ⊆ prefixChores := by
    intro chore hchore
    exact hcanonical.1.1 0 chore hchore
  have hownEq : ownSmallChoreSet cost (prefixAllocation 0) 0 =
      ownSmallChoreSet cost prefixChores 0 :=
    ownSmallChoreSet_eq_of_subset_and_card cost 0 hprefixOwnSubset hcanonicalOwn
  have hownCost : additiveChoreCost cost 0 (prefixAllocation 0) ≤ (a : ℝ) * r := by
    calc
      additiveChoreCost cost 0 (prefixAllocation 0) ≤ (prefixAllocation 0).card • r :=
        additiveChoreCost_le_card_nsmul_of_le cost 0 (prefixAllocation 0) r
          (fun chore hchore => IsOneOrRChoreCost.le_r cost r hcost (by linarith) 0 chore)
      _ = (a : ℝ) * r := by rw [hcanonical.2 0 |>.1, hquota0]; simp [nsmul_eq_mul]
  have hsuperZero (comparison : Fin 4) (hcomparisonNe : comparison ≠ 0)
      (hcomparisonQuota : quota comparison = a + 1) :
      additiveChoreCost cost 0 (prefixAllocation 0) ≤
        additiveChoreCost cost 0 (prefixAllocation comparison) - r := by
    have hcomparisonLarge : ∀ chore ∈ prefixAllocation comparison, cost 0 chore = r := by
      intro chore hchore
      rcases hcost 0 chore with hsmall | hlarge
      · exfalso
        have hchorePool : chore ∈ prefixChores :=
          hcanonical.1.1 comparison chore hchore
        have hown : chore ∈ ownSmallChoreSet cost prefixChores 0 :=
          Finset.mem_filter.mpr ⟨hchorePool, hsmall⟩
        have hzeroSmall : chore ∈ ownSmallChoreSet cost (prefixAllocation 0) 0 := by
          rw [hownEq]
          exact hown
        have hzeroOwn : chore ∈ prefixAllocation 0 :=
          (Finset.mem_filter.mp hzeroSmall).1
        exact hcomparisonNe
          (isAllocationOf_owner_unique hcanonical.1 hchorePool hchore hzeroOwn)
      · exact hlarge
    have hcomparisonCost : additiveChoreCost cost 0 (prefixAllocation comparison) =
        (a + 1 : ℕ) • r := by
      rw [additiveChoreCost_eq_card_nsmul_of_constant cost 0
        (prefixAllocation comparison) r hcomparisonLarge,
        hcanonical.2 comparison |>.1, hcomparisonQuota]
    simp only [nsmul_eq_mul] at hcomparisonCost
    calc
      additiveChoreCost cost 0 (prefixAllocation 0) ≤ (a : ℝ) * r := hownCost
      _ = ((a + 1 : ℕ) : ℝ) * r - r := by push_cast; ring
      _ = additiveChoreCost cost 0 (prefixAllocation comparison) - r := by
        rw [hcomparisonCost]
  apply hnotSuper
  intro own comparison hownQuota hcomparisonQuota
  have hownZero : own = 0 := by
    fin_cases own
    · rfl
    · have honeQuota : quota 1 = a := by simpa using hownQuota
      rw [hquota1] at honeQuota
      omega
    · have htwoQuota : quota 2 = a := by simpa using hownQuota
      rw [hquota2] at htwoQuota
      omega
    · have hthreeQuota : quota 3 = a := by simpa using hownQuota
      rw [hquota3] at hthreeQuota
      omega
  subst own
  have hcomparisonNe : comparison ≠ 0 := by
    intro hcomparisonZero
    subst comparison
    rw [hquota0] at hcomparisonQuota
    omega
  exact hsuperZero comparison hcomparisonNe hcomparisonQuota

/-- The canonical-prefix switch in source Case B.4.1(b).  Starting from a
non-super-canonical prefix with agent `0` short, reselect agent `1` as short.
The preceding cardinal consequence makes the now-long bundle of agent `0`
entirely small, which is the invariant needed by the one-item gap fill. -/
theorem existsB3IntersectingNonsupercanonicalPrefix
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores : Finset Item) (a : ℕ) (oldQuota : Fin 4 → ℕ)
    (oldAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (holdCanonical : IsCanonicalSmallChoreAllocation cost prefixChores oldQuota oldAllocation)
    (holdQuota0 : oldQuota 0 = a) (holdQuota1 : oldQuota 1 = a + 1)
    (holdQuota2 : oldQuota 2 = a + 1) (holdQuota3 : oldQuota 3 = a + 1)
    (hnotSuper : ¬ ∀ own comparison, oldQuota own = a → oldQuota comparison = a + 1 →
      additiveChoreCost cost own (oldAllocation own) ≤
        additiveChoreCost cost own (oldAllocation comparison) - r) :
    ∃ quota allocation,
      IsCanonicalSmallChoreAllocation cost prefixChores quota allocation ∧
      quota 0 = a + 1 ∧ quota 1 = a ∧ quota 2 = a + 1 ∧ quota 3 = a + 1 ∧
      (∀ chore ∈ allocation 0, IsSmallChore cost 0 chore) := by
  classical
  let quota : Fin 4 → ℕ := canonicalQuota a (Finset.univ \ {1})
  have hlongCard : (Finset.univ \ ({1} : Finset (Fin 4))).card = 3 := by decide
  have hquotaSum : Finset.univ.sum quota = prefixChores.card := by
    rw [show quota = canonicalQuota a (Finset.univ \ {1}) by rfl, canonicalQuota_sum,
      hlongCard, hprefixCard]
  obtain ⟨allocation, hcanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores quota hquotaSum hprefixSmall
  have holdSmallCard : a + 1 ≤ (ownSmallChoreSet cost prefixChores 0).card :=
    ownSmallCard_succ_le_of_not_supercanonical_zero_short Item r cost prefixChores a
      oldQuota oldAllocation hr hcost holdCanonical holdQuota0 holdQuota1 holdQuota2
      holdQuota3 hnotSuper
  have hquota0 : quota 0 = a + 1 := by simp [quota, canonicalQuota]
  have hquota1 : quota 1 = a := by simp [quota, canonicalQuota]
  have hquota2 : quota 2 = a + 1 := by simp [quota, canonicalQuota]
  have hquota3 : quota 3 = a + 1 := by simp [quota, canonicalQuota]
  have hcanonicalOwn : (ownSmallChoreSet cost (allocation 0) 0).card = a + 1 := by
    rw [hcanonical.2 0 |>.2, hquota0, Nat.min_eq_left holdSmallCard]
  have hownEq : ownSmallChoreSet cost (allocation 0) 0 = allocation 0 := by
    apply Finset.eq_of_subset_of_card_le
    · intro chore hchore
      exact (Finset.mem_filter.mp hchore).1
    · rw [hcanonicalOwn, hcanonical.2 0 |>.1, hquota0]
  refine ⟨quota, allocation, hcanonical, hquota0, hquota1, hquota2, hquota3, ?_⟩
  intro chore hchore
  have hsmallOwn : chore ∈ ownSmallChoreSet cost (allocation 0) 0 := by
    rw [hownEq]
    exact hchore
  exact (Finset.mem_filter.mp hsmallOwn).2

/-- Source Case B.4.1(b) after its finite exceptional-residue classification.
The previous theorem constructs the switched canonical prefix directly from
the source's failed-super-canonicity premise; the two compiled residual kernels
then discharge the nonexceptional and `(0,2)` exceptional outcomes. -/
theorem existsEfxOfM01M2_b3_intersecting_nonsupercanonical
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (oldQuota : Fin 4 → ℕ)
    (oldAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (holdCanonical : IsCanonicalSmallChoreAllocation cost prefixChores oldQuota oldAllocation)
    (holdQuota0 : oldQuota 0 = a) (holdQuota1 : oldQuota 1 = a + 1)
    (holdQuota2 : oldQuota 2 = a + 1) (holdQuota3 : oldQuota 3 = a + 1)
    (hnotSuper : ¬ ∀ own comparison, oldQuota own = a → oldQuota comparison = a + 1 →
      additiveChoreCost cost own (oldAllocation own) ≤
        additiveChoreCost cost own (oldAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hresidual : ¬ IsM2Exceptional cost (m2Chores \ {item}) ∨
      IsM2ExceptionalWithEndpoints cost (m2Chores \ {item}) 0 2) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨quota, prefixAllocation, hcanonical, hquota0, hquota1, hquota2, hquota3,
    hprefixZeroSmall⟩ :=
    existsB3IntersectingNonsupercanonicalPrefix Item r cost prefixChores a oldQuota
      oldAllocation hr hcost hprefixCard hprefixSmall holdCanonical holdQuota0 holdQuota1
      holdQuota2 holdQuota3 hnotSuper
  rcases hresidual with hnotExceptional | hexceptional
  · exact existsEfxOfM01M2_b3_intersecting_nonsupercanonical_nonexceptional Item r cost
      prefixChores m2Chores a quota prefixAllocation item hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hitem hprefixZeroSmall hm2Small hnotExceptional
  · exact existsEfxOfM01M2_b3_intersecting_nonsupercanonical_exceptional Item r cost
      prefixChores m2Chores a quota prefixAllocation item hr hcost hprefixM2 hprefixSmall
      hcanonical hquota0 hquota1 hquota2 hquota3 hitem hprefixZeroSmall hexceptional

/-- The residual classification in source Case B.4.1(b).  The chosen
type-`(0,1)` fibre is at least as large as every other fibre, and the
unremoved type-`(0,2)` chore survives.  An exceptional residue must therefore
use that latter type as its single auxiliary chore, so its auxiliary endpoints
are exactly `(0,2)`. -/
theorem b3_intersecting_nonsupercanonical_exceptional_auxiliary_pair
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second : Item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card)
    (hexceptional : IsM2Exceptional cost (m2Chores \ {first})) :
    IsM2ExceptionalWithEndpoints cost (m2Chores \ {first}) 0 2 := by
  classical
  let residue : Finset Item := m2Chores \ {first}
  let firstType : Finset Item :=
    m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))
  have htypesNe : ({0, 1} : Finset (Fin 4)) ≠ {0, 2} := by
    intro heq
    have hone : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by simp
    rw [heq] at hone
    norm_num at hone
    have honeNat : (1 : ℕ) = 2 := congrArg Fin.val hone
    omega
  have hfirstNeSecond : first ≠ second := by
    intro heq
    subst second
    exact (Finset.disjoint_left.mp
      (m2TypeChorePool_disjoint_of_ne cost m2Chores
        ({0, 1} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4)) htypesNe) hfirst hsecond).elim
  have hdominantLarge : ∀ dominant auxiliary : Finset (Fin 4), ∀ q : ℕ,
      dominant.card = 2 → auxiliary.card = 2 → Disjoint dominant auxiliary →
      (((∀ item ∈ residue, smallAgentSet cost item = dominant) ∧
          residue.card = 4 * q + 3) ∨
        (∃ exceptionalItem ∈ residue, smallAgentSet cost exceptionalItem = auxiliary ∧
          (∀ item ∈ residue.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
          (residue.erase exceptionalItem).card = 4 * q + 3)) →
      3 ≤ (m2TypeChorePool cost m2Chores dominant).card := by
    intro dominant auxiliary q _hdominant _hauxiliary _hdisjoint hshape
    rcases hshape with hfixed | hsingle
    · have hsubset : residue ⊆ m2TypeChorePool cost m2Chores dominant := by
        intro item hitem
        have hitemBase : item ∈ m2Chores := by
          have hitem' : item ∈ m2Chores \ {first} := by
            simpa [residue] using hitem
          exact Finset.sdiff_subset hitem'
        exact (mem_m2TypeChorePool cost m2Chores dominant item).mpr
          ⟨hitemBase, hfixed.1 item hitem⟩
      have hcard := Finset.card_le_card hsubset
      rw [hfixed.2] at hcard
      omega
    · obtain ⟨exceptionalItem, _hexceptionalItem, _hitemType, houtsideType,
          houtsideCard⟩ := hsingle
      have hsubset : residue.erase exceptionalItem ⊆
          m2TypeChorePool cost m2Chores dominant := by
        intro item hitem
        exact (mem_m2TypeChorePool cost m2Chores dominant item).mpr
          ⟨Finset.sdiff_subset (Finset.erase_subset exceptionalItem residue hitem),
            houtsideType item hitem⟩
      have hcard := Finset.card_le_card hsubset
      rw [houtsideCard] at hcard
      omega
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hshape⟩
  have hdominantPoolLarge : 3 ≤ (m2TypeChorePool cost m2Chores dominant).card :=
    hdominantLarge dominant auxiliary q hdominant hauxiliary hdisjoint
      (by simpa [residue] using hshape)
  have hfirstTypeCard : 3 ≤ firstType.card :=
    hdominantPoolLarge.trans (by simpa [firstType] using hmaximum dominant)
  have hfirstTypeMem : first ∈ firstType := by simpa [firstType] using hfirst
  have hsurvivorCard : 2 ≤ (firstType.erase first).card := by
    rw [Finset.card_erase_of_mem hfirstTypeMem]
    omega
  obtain ⟨survivors, hsurvivorSubset, hsurvivorsCard⟩ :=
    (firstType.erase first).exists_subset_card_eq hsurvivorCard
  obtain ⟨survivorOne, survivorTwo, hsurvivorsNe, hsurvivorsEq⟩ :=
    Finset.card_eq_two.mp hsurvivorsCard
  have hsurvivorOneErase : survivorOne ∈ firstType.erase first := by
    apply hsurvivorSubset
    simp [hsurvivorsEq]
  have hsurvivorTwoErase : survivorTwo ∈ firstType.erase first := by
    apply hsurvivorSubset
    simp [hsurvivorsEq]
  have hsurvivorOneType : survivorOne ∈ firstType :=
    (Finset.mem_erase.mp hsurvivorOneErase).2
  have hsurvivorTwoType : survivorTwo ∈ firstType :=
    (Finset.mem_erase.mp hsurvivorTwoErase).2
  have hsurvivorOneNeFirst : survivorOne ≠ first := (Finset.mem_erase.mp hsurvivorOneErase).1
  have hsurvivorTwoNeFirst : survivorTwo ≠ first := (Finset.mem_erase.mp hsurvivorTwoErase).1
  have hsurvivorOneResidue : survivorOne ∈ residue := by
    refine Finset.mem_sdiff.mpr ⟨?_, by simpa using hsurvivorOneNeFirst⟩
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) survivorOne).mp
      (by simpa [firstType] using hsurvivorOneType) |>.1
  have hsurvivorTwoResidue : survivorTwo ∈ residue := by
    refine Finset.mem_sdiff.mpr ⟨?_, by simpa using hsurvivorTwoNeFirst⟩
    exact (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) survivorTwo).mp
      (by simpa [firstType] using hsurvivorTwoType) |>.1
  have hsurvivorOneSmall : smallAgentSet cost survivorOne = ({0, 1} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) survivorOne).mp
      (by simpa [firstType] using hsurvivorOneType) |>.2
  have hsurvivorTwoSmall : smallAgentSet cost survivorTwo = ({0, 1} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) survivorTwo).mp
      (by simpa [firstType] using hsurvivorTwoType) |>.2
  have hsecondResidue : second ∈ residue := by
    refine Finset.mem_sdiff.mpr ⟨?_, by simpa using hfirstNeSecond.symm⟩
    exact (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) second).mp hsecond |>.1
  have hsecondSmall : smallAgentSet cost second = ({0, 2} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)) second).mp hsecond |>.2
  have hauxiliaryEq : auxiliary = ({0, 2} : Finset (Fin 4)) := by
    rcases hshape with hfixed | hsingle
    · have hdominantFirst : dominant = ({0, 1} : Finset (Fin 4)) :=
        (hfixed.1 survivorOne hsurvivorOneResidue).symm.trans hsurvivorOneSmall
      have hdominantSecond : dominant = ({0, 2} : Finset (Fin 4)) :=
        (hfixed.1 second hsecondResidue).symm.trans hsecondSmall
      exact False.elim (htypesNe (hdominantFirst.symm.trans hdominantSecond))
    · obtain ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType,
        _houtsideCard⟩ := hsingle
      by_cases hsecondExceptional : second = exceptionalItem
      · subst exceptionalItem
        exact hitemType.symm.trans hsecondSmall
      · have hdominantSecond : dominant = ({0, 2} : Finset (Fin 4)) :=
          ((houtsideType second
            (Finset.mem_erase.mpr ⟨hsecondExceptional, hsecondResidue⟩)).symm).trans
              hsecondSmall
        obtain ⟨survivor, hsurvivorResidue, hsurvivorSmall, hsurvivorNeExceptional⟩ :
            ∃ survivor ∈ residue,
              smallAgentSet cost survivor = ({0, 1} : Finset (Fin 4)) ∧
              survivor ≠ exceptionalItem := by
          by_cases hsurvivorOneExceptional : survivorOne = exceptionalItem
          · refine ⟨survivorTwo, hsurvivorTwoResidue, hsurvivorTwoSmall, ?_⟩
            intro hsurvivorTwoExceptional
            apply hsurvivorsNe
            rw [hsurvivorOneExceptional, hsurvivorTwoExceptional]
          · exact ⟨survivorOne, hsurvivorOneResidue, hsurvivorOneSmall,
              hsurvivorOneExceptional⟩
        have hdominantFirst : dominant = ({0, 1} : Finset (Fin 4)) :=
          ((houtsideType survivor
            (Finset.mem_erase.mpr ⟨hsurvivorNeExceptional, hsurvivorResidue⟩)).symm).trans
              hsurvivorSmall
        exact False.elim (htypesNe (hdominantFirst.symm.trans hdominantSecond))
  refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_, hshape⟩
  · simp [hauxiliaryEq]
  · simp [hauxiliaryEq]

/-- The B.4.1(b) dispatcher is complete when the selected intersecting
type-`(0,1)` fibre is a global maximum fibre.  This is the source's
non-super-canonical prefix switch followed by the finite residual
classification above. -/
theorem existsEfxOfM01M2_b3_intersecting_nonsupercanonical_of_maximum
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (oldQuota : Fin 4 → ℕ)
    (oldAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (holdCanonical : IsCanonicalSmallChoreAllocation cost prefixChores oldQuota oldAllocation)
    (holdQuota0 : oldQuota 0 = a) (holdQuota1 : oldQuota 1 = a + 1)
    (holdQuota2 : oldQuota 2 = a + 1) (holdQuota3 : oldQuota 3 = a + 1)
    (hnotSuper : ¬ ∀ own comparison, oldQuota own = a → oldQuota comparison = a + 1 →
      additiveChoreCost cost own (oldAllocation own) ≤
        additiveChoreCost cost own (oldAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (second : Item)
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {item})
  · exact existsEfxOfM01M2_b3_intersecting_nonsupercanonical Item r cost
      prefixChores m2Chores a oldQuota oldAllocation item hr hcost hprefixM2 hprefixCard
      hprefixSmall holdCanonical holdQuota0 holdQuota1 holdQuota2 holdQuota3 hnotSuper
      hitem hm2Small (Or.inl hnotExceptional)
  exact existsEfxOfM01M2_b3_intersecting_nonsupercanonical Item r cost
    prefixChores m2Chores a oldQuota oldAllocation item hr hcost hprefixM2 hprefixCard
    hprefixSmall holdCanonical holdQuota0 holdQuota1 holdQuota2 holdQuota3 hnotSuper hitem
    hm2Small (Or.inr
      (b3_intersecting_nonsupercanonical_exceptional_auxiliary_pair Item cost m2Chores
        item second hitem hsecond hmaximum (not_not.mp hnotExceptional)))

/-- The two-item gap prefix in source Case B.4.2(a).  A type-`(0,1)` and a
type-`(2,3)` chore are given to the unique short agent `0`.  Every observer
sees one small and one large added chore, hence cost `r + 1`; super-canonicity
then yields the displayed short-unit and long-prefix comparisons. -/
theorem existsGapFill_b3_disjoint_shortEndpoint
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))) :
    ∃ gap : Allocation (Fin 4) Item,
      IsAllocationOf gap ({first, second} : Finset Item) ∧
      (∀ agent, agent ≠ 0 → gap agent = ∅) ∧
      (∀ agent, additiveChoreCost cost agent (gap 0) = r + 1) ∧
      (∀ other, additiveChoreCost cost 0 (prefixAllocation 0 ∪ gap 0) - 1 ≤
        additiveChoreCost cost 0 (prefixAllocation other ∪ gap other)) ∧
      (∀ own, own ≠ 0 → ∀ comparison, comparison ≠ 0 →
        additiveChoreCost cost own (prefixAllocation own ∪ gap own) ≤
          additiveChoreCost cost own (prefixAllocation comparison ∪ gap comparison)) ∧
      (∀ own, own ≠ 0 →
        additiveChoreCost cost own (prefixAllocation own ∪ gap own) ≤
          additiveChoreCost cost own (prefixAllocation 0 ∪ gap 0)) := by
  classical
  let gap : Allocation (Fin 4) Item := allocateAllTo (Fin 4) Item 0 ({first, second} : Finset Item)
  have hfirstM2 : first ∈ m2Chores := (mem_m2TypeChorePool cost m2Chores
    ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores := (mem_m2TypeChorePool cost m2Chores
    ({2, 3} : Finset (Fin 4)) second).mp hsecond |>.1
  have hfirstType : smallAgentSet cost first = ({0, 1} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.2
  have hsecondType : smallAgentSet cost second = ({2, 3} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) second).mp hsecond |>.2
  have hne : first ≠ second := by
    intro heq
    rw [heq, hsecondType] at hfirstType
    have hmem := congrArg (fun agents : Finset (Fin 4) => (2 : Fin 4) ∈ agents) hfirstType
    norm_num at hmem
    omega
  have hfirstSmallZero : cost 0 first = 1 := by
    have hmem : (0 : Fin 4) ∈ smallAgentSet cost first := by rw [hfirstType]; simp
    simpa [smallAgentSet] using hmem
  have hfirstSmallOne : cost 1 first = 1 := by
    have hmem : (1 : Fin 4) ∈ smallAgentSet cost first := by rw [hfirstType]; simp
    simpa [smallAgentSet] using hmem
  have hsecondSmallTwo : cost 2 second = 1 := by
    have hmem : (2 : Fin 4) ∈ smallAgentSet cost second := by rw [hsecondType]; simp
    simpa [smallAgentSet] using hmem
  have hsecondSmallThree : cost 3 second = 1 := by
    have hmem : (3 : Fin 4) ∈ smallAgentSet cost second := by rw [hsecondType]; simp
    simpa [smallAgentSet] using hmem
  have cost_eq_r_of_not_small (agent : Fin 4) (item : Item)
      (hnot : agent ∉ smallAgentSet cost item) : cost agent item = r := by
    rcases hcost agent item with hsmall | hlarge
    · exfalso
      apply hnot
      simpa [smallAgentSet] using hsmall
    · exact hlarge
  have hfirstLargeTwo : cost 2 first = r :=
    cost_eq_r_of_not_small 2 first (by rw [hfirstType]; simp)
  have hfirstLargeThree : cost 3 first = r :=
    cost_eq_r_of_not_small 3 first (by rw [hfirstType]; simp)
  have hsecondLargeZero : cost 0 second = r :=
    cost_eq_r_of_not_small 0 second (by rw [hsecondType]; simp)
  have hsecondLargeOne : cost 1 second = r :=
    cost_eq_r_of_not_small 1 second (by rw [hsecondType]; simp)
  have hgapAllocation : IsAllocationOf gap ({first, second} : Finset Item) :=
    isAllocationOf_allocateAllTo 0 ({first, second} : Finset Item)
  have hgapZero : gap 0 = ({first, second} : Finset Item) := by simp [gap, allocateAllTo]
  have hgapOther : ∀ agent : Fin 4, agent ≠ 0 → gap agent = ∅ := by
    intro agent hneZero
    simp [gap, allocateAllTo, hneZero]
  have hgapCost : ∀ agent : Fin 4, additiveChoreCost cost agent (gap 0) = r + 1 := by
    intro agent
    fin_cases agent <;> rw [hgapZero] <;>
      simp [additiveChoreCost, hne, hfirstSmallZero, hfirstSmallOne, hfirstLargeTwo,
        hfirstLargeThree, hsecondLargeZero, hsecondLargeOne, hsecondSmallTwo,
        hsecondSmallThree] <;> ring
  have hprefixGap : Disjoint prefixChores ({first, second} : Finset Item) := by
    rw [Finset.disjoint_left]
    intro item hprefix hgap
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgap
    rcases hgap with rfl | rfl
    · exact (Finset.disjoint_left.mp hprefixM2 hprefix hfirstM2).elim
    · exact (Finset.disjoint_left.mp hprefixM2 hprefix hsecondM2).elim
  have hbundleDisjoint : ∀ agent, Disjoint (prefixAllocation agent) (gap agent) := by
    intro agent
    exact Disjoint.mono (hcanonical.1.1 agent) (hgapAllocation.1 agent) hprefixGap
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (hbundleDisjoint owner)
  have hquotaLong : ∀ agent : Fin 4, agent ≠ 0 → quota agent = a + 1 := by
    intro agent hneZero
    fin_cases agent
    · exact (hneZero rfl).elim
    · exact hquota1
    · exact hquota2
    · exact hquota3
  have hquotaBalanced : ∀ i j : Fin 4, quota i ≤ quota j + 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  refine ⟨gap, hgapAllocation, hgapOther, hgapCost, ?_, ?_, ?_⟩
  · intro other
    by_cases hother : other = 0
    · subst other
      linarith
    · rw [hleftCost 0 0, hleftCost 0 other, hgapCost 0, hgapOther other hother]
      simp only [additiveChoreCost_empty, add_zero]
      linarith [hsuper 0 other hquota0 (hquotaLong other hother)]
  · intro own hown comparison hcomparison
    rw [hleftCost own own, hleftCost own comparison, hgapOther own hown,
      hgapOther comparison hcomparison]
    simp only [additiveChoreCost_empty, add_zero]
    exact hcanonical.envyFreeForChores_of_quota_eq cost r prefixChores quota prefixAllocation
      hcost (by linarith) own comparison
      ((hquotaLong own hown).trans (hquotaLong comparison hcomparison).symm)
  · intro own hown
    rw [hleftCost own own, hleftCost own 0, hgapOther own hown, hgapCost own]
    simp only [additiveChoreCost_empty, add_zero]
    linarith [hprefixEFX.additive_le_additive_add_r cost r prefixAllocation hcost
      (by linarith) own 0]

/-- The nonexceptional branch of source Case B.4.2(a).  The two-gap prefix
has one-unit slack only at short agent `0`; the strengthened preferred M₂
allocation makes the same agent residual-favorite, while retaining all
small-removal certificates for the other comparisons. -/
theorem existsEfxOfM01M2_b3_disjoint_shortEndpoint_nonexceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (htypes : ∀ item ∈ m2Chores,
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)))
    (hresidueCount : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet cost item = ({0, 1} : Finset (Fin 4))).card ≤
      ((m2Chores \ {first, second}).filter
        fun item => smallAgentSet cost item = ({2, 3} : Finset (Fin 4))).card)
    (hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, _hgapOther, _hgapCost, hleftShort, hleftOther, hleftToShort⟩ :=
    existsGapFill_b3_disjoint_shortEndpoint Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hsuper hfirst hsecond
  have hfirstM2 : first ∈ m2Chores := (mem_m2TypeChorePool cost m2Chores
    ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores := (mem_m2TypeChorePool cost m2Chores
    ({2, 3} : Finset (Fin 4)) second).mp hsecond |>.1
  have hresidueTypes : ∀ item ∈ m2Chores \ {first, second},
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)) := by
    intro item hitem
    exact htypes item (Finset.sdiff_subset hitem)
  obtain ⟨right, hrightAllocation, _hrightEfx, hsmallCertificate, hlargeCertificate,
    hrightFavorite⟩ :=
    existsEfxOfM2TwoDisjointTypes_preferred_certified_of_notExceptional Item r cost
      (m2Chores \ {first, second}) ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) 0
      hr hcost (by decide) (by decide) (by decide) hresidueTypes hresidueCount (by simp)
      hnotExceptional
  have hunit : ∀ agent other,
      additiveChoreCost cost agent (right agent) - 1 ≤
        additiveChoreCost cost agent (right other) := by
    intro agent other
    by_cases hsmall : ∃ item ∈ right agent, IsSmallChore cost agent item
    · exact hsmallCertificate agent hsmall other
    · have hlarge : ∀ item ∈ right agent, IsLargeChore cost r agent item := by
        intro item hitem
        rcases hcost agent item with hsmallItem | hlargeItem
        · exact (hsmall ⟨item, hitem, by simpa [IsSmallChore] using hsmallItem⟩).elim
        · simpa [IsLargeChore] using hlargeItem
      linarith [hlargeCertificate agent hlarge other]
  have hgapSubset : ({first, second} : Finset Item) ⊆ m2Chores := by
    intro item hitem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hitem
    rcases hitem with rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
  have hprefixGap : Disjoint prefixChores ({first, second} : Finset Item) :=
    hprefixM2.mono_right hgapSubset
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ ({first, second} : Finset Item)) :=
    isAllocationOf_union prefixAllocation gap prefixChores ({first, second} : Finset Item)
      hprefixGap hcanonical.1 hgapAllocation
  have hgapResidue : Disjoint ({first, second} : Finset Item) (m2Chores \ {first, second}) :=
    Finset.disjoint_sdiff
  have hgapResidueUnion : ({first, second} : Finset Item) ∪ (m2Chores \ {first, second}) = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores (m2Chores \ {first, second}) :=
    hprefixM2.mono_right Finset.sdiff_subset
  have hleftResidue : Disjoint (prefixChores ∪ ({first, second} : Finset Item))
      (m2Chores \ {first, second}) := by
    rw [Finset.disjoint_left]
    intro item hleftMem hresidue
    rcases Finset.mem_union.mp hleftMem with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue hprefix hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgap hresidue).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleftMem hrightMem
    have hresidue := hrightAllocation.1 agent item hrightMem
    rcases Finset.mem_union.mp hleftMem with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue (hcanonical.1.1 agent item hprefix) hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue (hgapAllocation.1 agent item hgap) hresidue).elim
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right
      (prefixChores ∪ ({first, second} : Finset Item)) (m2Chores \ {first, second})
      hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ ({first, second} : Finset Item)) ∪
        (m2Chores \ {first, second}) = prefixChores ∪ m2Chores := by
      calc
        (prefixChores ∪ ({first, second} : Finset Item)) ∪ (m2Chores \ {first, second}) =
            prefixChores ∪ (({first, second} : Finset Item) ∪ (m2Chores \ {first, second})) :=
          Finset.union_assoc _ _ _
        _ = prefixChores ∪ m2Chores := by rw [hgapResidueUnion]
    rw [← hgoods]
    exact hcombined
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efxForChores_union_of_short_unit_slack_and_right_favorite cost left right 0
    hbundlesDisjoint hcostLower (by simpa [left] using hleftShort)
    (by simpa [left] using hleftOther) (by simpa [left] using hleftToShort)
    hunit hrightFavorite

/-- In source Case B.4.2(a), after one chore of each disjoint type is removed,
the residual multiplicity inequality rules out an exceptional residue whose
dominant type is `(0,1)`.  Hence its auxiliary (exceptional) pair is exactly
`(0,1)`. -/
theorem b3_disjoint_short_exceptional_auxiliary_pair
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (residue : Finset Item)
    (htypes : ∀ item ∈ residue,
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)))
    (hcount : (residue.filter fun item => smallAgentSet cost item =
      ({0, 1} : Finset (Fin 4))).card ≤
      (residue.filter fun item => smallAgentSet cost item =
        ({2, 3} : Finset (Fin 4))).card)
    (hexceptional : IsM2Exceptional cost residue) :
    IsM2ExceptionalWithEndpoints cost residue 0 1 := by
  classical
  let type01 : Finset (Fin 4) := {0, 1}
  let type23 : Finset (Fin 4) := {2, 3}
  have htypesNe : type01 ≠ type23 := by decide
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hshape⟩
  have hauxiliaryOfDominant23 (hdominantEq : dominant = type23) :
      auxiliary = type01 := by
    have hsubset : auxiliary ⊆ type23ᶜ := by
      intro agent hagent
      simp only [Finset.mem_compl]
      intro hdominantMem
      exact Finset.disjoint_left.mp hdisjoint (by simpa [hdominantEq] using hdominantMem)
        hagent
    have hauxiliaryCompl : auxiliary = type23ᶜ := by
      apply Finset.eq_of_subset_of_card_le hsubset
      have hcomplementCard : type23ᶜ.card = 2 := by decide
      rw [hcomplementCard, hauxiliary]
    calc
      auxiliary = type23ᶜ := hauxiliaryCompl
      _ = type01 := by decide
  have hdominantNe01 : dominant ≠ type01 := by
    intro hdominantEq
    rcases hshape with hfixed | hsingle
    · obtain ⟨hfixedType, hresidueCard⟩ := hfixed
      have hfirstAll : residue.filter (fun item => smallAgentSet cost item = type01) = residue := by
        apply Finset.filter_eq_self.mpr
        intro item hitem
        rw [← hdominantEq]
        exact hfixedType item hitem
      have hsecondEmpty : residue.filter (fun item => smallAgentSet cost item = type23) = ∅ := by
        ext item
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hitemResidue, hitemType⟩
          exact (htypesNe ((hfixedType item hitemResidue).trans hdominantEq |>.symm.trans hitemType)).elim
        · intro hitem
          simp at hitem
      have hcount' : residue.card ≤ 0 := by
        simpa [type01, type23, hfirstAll, hsecondEmpty] using hcount
      rw [hresidueCard] at hcount'
      omega
    · obtain ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType,
        houtsideCard⟩ := hsingle
      have hfirstLarge : 3 ≤
          (residue.filter fun item => smallAgentSet cost item = type01).card := by
        have hsubset : residue.erase exceptionalItem ⊆
            residue.filter fun item => smallAgentSet cost item = type01 := by
          intro item hitem
          exact Finset.mem_filter.mpr ⟨Finset.erase_subset exceptionalItem residue hitem,
            (houtsideType item hitem).trans hdominantEq⟩
        have hcard := Finset.card_le_card hsubset
        rw [houtsideCard] at hcard
        omega
      have hsecondSmall :
          (residue.filter fun item => smallAgentSet cost item = type23).card ≤ 1 := by
        have hsubset : residue.filter (fun item => smallAgentSet cost item = type23) ⊆
            ({exceptionalItem} : Finset Item) := by
          intro item hitem
          by_cases hitemExceptional : item = exceptionalItem
          · simp [hitemExceptional]
          · have hmem := Finset.mem_filter.mp hitem
            have houtside : item ∈ residue.erase exceptionalItem :=
              Finset.mem_erase.mpr ⟨hitemExceptional, hmem.1⟩
            exact (htypesNe ((houtsideType item houtside).trans hdominantEq |>.symm.trans hmem.2)).elim
        calc
          (residue.filter fun item => smallAgentSet cost item = type23).card ≤
              ({exceptionalItem} : Finset Item).card := Finset.card_le_card hsubset
          _ = 1 := by simp
      have hcount' :
          (residue.filter fun item => smallAgentSet cost item = type01).card ≤
            (residue.filter fun item => smallAgentSet cost item = type23).card := by
        simpa [type01, type23] using hcount
      omega
  have hdominantEq : dominant = type23 := by
    rcases hshape with hfixed | hsingle
    · obtain ⟨hfixedType, hresidueCard⟩ := hfixed
      have hpositive : 0 < residue.card := by rw [hresidueCard]; omega
      obtain ⟨item, hitem⟩ := Finset.card_pos.mp hpositive
      rcases htypes item hitem with htype | htype
      · exact (hdominantNe01 (hfixedType item hitem |>.symm.trans htype)).elim
      · exact (hfixedType item hitem).symm.trans htype
    · obtain ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType,
        houtsideCard⟩ := hsingle
      have hpositive : 0 < (residue.erase exceptionalItem).card := by
        rw [houtsideCard]
        omega
      obtain ⟨item, hitem⟩ := Finset.card_pos.mp hpositive
      have hitemResidue : item ∈ residue := Finset.erase_subset exceptionalItem residue hitem
      rcases htypes item hitemResidue with htype | htype
      · exact (hdominantNe01 (houtsideType item hitem |>.symm.trans htype)).elim
      · exact (houtsideType item hitem).symm.trans htype
  refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_, hshape⟩
  · rw [hauxiliaryOfDominant23 hdominantEq]
    simp [type01]
  · rw [hauxiliaryOfDominant23 hdominantEq]
    simp [type01]

/-- The exceptional branch of source Case B.4.2(a).  The two gap chores go to
short agent `0`; the classified exceptional residue is allocated with agent
`0` residual-favorite and agent `1` as the sole controlled all-large endpoint.
The source's small-prefix split supplies the remaining `r - 1` comparison. -/
theorem existsEfxOfM01M2_b3_disjoint_shortEndpoint_exceptional
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (htypes : ∀ item ∈ m2Chores,
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)))
    (hresidueCount : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet cost item = ({0, 1} : Finset (Fin 4))).card ≤
      ((m2Chores \ {first, second}).filter
        fun item => smallAgentSet cost item = ({2, 3} : Finset (Fin 4))).card)
    (hexceptional : IsM2Exceptional cost (m2Chores \ {first, second})) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨gap, hgapAllocation, hgapOther, hgapCost, hleftShort, hleftOther, hleftToShort⟩ :=
    existsGapFill_b3_disjoint_shortEndpoint Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3
      hsuper hfirst hsecond
  have hfirstM2 : first ∈ m2Chores := (mem_m2TypeChorePool cost m2Chores
    ({0, 1} : Finset (Fin 4)) first).mp hfirst |>.1
  have hsecondM2 : second ∈ m2Chores := (mem_m2TypeChorePool cost m2Chores
    ({2, 3} : Finset (Fin 4)) second).mp hsecond |>.1
  have hresidueTypes : ∀ item ∈ m2Chores \ {first, second},
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)) := by
    intro item hitem
    exact htypes item (Finset.sdiff_subset hitem)
  obtain ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, hzero, hone, hshape⟩ :=
    b3_disjoint_short_exceptional_auxiliary_pair Item cost (m2Chores \ {first, second})
      hresidueTypes hresidueCount hexceptional
  obtain ⟨right, hrightAllocation, hunit, hrightLarge, hrightAway, hrightComparison,
    hrightFavorite⟩ :=
    existsExceptionalM2Allocation_controlled_with_companionFavorite Item r cost
      (m2Chores \ {first, second}) dominant auxiliary q (by linarith) hcost hdominant hauxiliary
      hdisjoint hshape 1 0 hone hzero (by decide)
  have hgapSubset : ({first, second} : Finset Item) ⊆ m2Chores := by
    intro item hitem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hitem
    rcases hitem with rfl | rfl
    · exact hfirstM2
    · exact hsecondM2
  have hprefixGap : Disjoint prefixChores ({first, second} : Finset Item) :=
    hprefixM2.mono_right hgapSubset
  let left : Allocation (Fin 4) Item := fun agent => prefixAllocation agent ∪ gap agent
  have hleftAllocation : IsAllocationOf left (prefixChores ∪ ({first, second} : Finset Item)) :=
    isAllocationOf_union prefixAllocation gap prefixChores ({first, second} : Finset Item)
      hprefixGap hcanonical.1 hgapAllocation
  have hgapResidue : Disjoint ({first, second} : Finset Item) (m2Chores \ {first, second}) :=
    Finset.disjoint_sdiff
  have hgapResidueUnion : ({first, second} : Finset Item) ∪ (m2Chores \ {first, second}) = m2Chores :=
    Finset.union_sdiff_of_subset hgapSubset
  have hprefixResidue : Disjoint prefixChores (m2Chores \ {first, second}) :=
    hprefixM2.mono_right Finset.sdiff_subset
  have hleftResidue : Disjoint (prefixChores ∪ ({first, second} : Finset Item))
      (m2Chores \ {first, second}) := by
    rw [Finset.disjoint_left]
    intro item hleftMem hresidue
    rcases Finset.mem_union.mp hleftMem with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue hprefix hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue hgap hresidue).elim
  have hbundlesDisjoint : ∀ agent, Disjoint (left agent) (right agent) := by
    intro agent
    rw [Finset.disjoint_left]
    intro item hleftMem hrightMem
    have hresidue := hrightAllocation.1 agent item hrightMem
    rcases Finset.mem_union.mp hleftMem with hprefix | hgap
    · exact (Finset.disjoint_left.mp hprefixResidue (hcanonical.1.1 agent item hprefix) hresidue).elim
    · exact (Finset.disjoint_left.mp hgapResidue (hgapAllocation.1 agent item hgap) hresidue).elim
  have hleftCost (observer owner : Fin 4) :
      additiveChoreCost cost observer (prefixAllocation owner ∪ gap owner) =
        additiveChoreCost cost observer (prefixAllocation owner) +
          additiveChoreCost cost observer (gap owner) :=
    additiveChoreCost_union cost observer (prefixAllocation owner) (gap owner)
      (Disjoint.mono (hcanonical.1.1 owner) (hgapAllocation.1 owner) hprefixGap)
  have hquotaBalanced : ∀ own comparison, quota own ≤ quota comparison + 1 := by
    intro own comparison
    fin_cases own <;> fin_cases comparison <;>
      simp [hquota0, hquota1, hquota2, hquota3] <;> omega
  have hprefixEFX : EFXForChores (additiveChoreCost cost) prefixAllocation :=
    hcanonical.efxForChores cost r prefixChores quota prefixAllocation hcost (by linarith)
      hquotaBalanced
  have hspecialLeft :
      (∀ item ∈ left 1, IsLargeChore cost r 1 item) ∨
        additiveChoreCost cost 1 (left 1) + (r - 1) ≤
          additiveChoreCost cost 1 (left 0) := by
    by_cases hsmall : ∃ item ∈ prefixAllocation 1, IsSmallChore cost 1 item
    · right
      obtain ⟨item, hitem, hitemSmall⟩ := hsmall
      have hprefixSlack := EFXForChores.additive_sub_one_le_of_small cost prefixAllocation
        hprefixEFX 1 0 item hitem hitemSmall
      change additiveChoreCost cost 1 (prefixAllocation 1 ∪ gap 1) + (r - 1) ≤
        additiveChoreCost cost 1 (prefixAllocation 0 ∪ gap 0)
      rw [hleftCost 1 1, hleftCost 1 0, hgapOther 1 (by decide), hgapCost 1]
      simp only [additiveChoreCost_empty, add_zero]
      linarith
    · left
      intro item hitem
      have hprefixItem : item ∈ prefixAllocation 1 := by
        simpa [left, hgapOther 1 (by decide)] using hitem
      rcases hcost 1 item with hsmallItem | hlargeItem
      · exact (hsmall ⟨item, hprefixItem, by simpa [IsSmallChore] using hsmallItem⟩).elim
      · simpa [IsLargeChore] using hlargeItem
  have hcostLower : ∀ agent item, 1 ≤ cost agent item :=
    fun agent item => IsOneOrRChoreCost.one_le cost r hcost (by linarith) agent item
  have hfinalAllocation : IsAllocationOf (fun agent => left agent ∪ right agent)
      (prefixChores ∪ m2Chores) := by
    have hcombined := isAllocationOf_union left right
      (prefixChores ∪ ({first, second} : Finset Item)) (m2Chores \ {first, second})
      hleftResidue hleftAllocation hrightAllocation
    have hgoods : (prefixChores ∪ ({first, second} : Finset Item)) ∪
        (m2Chores \ {first, second}) = prefixChores ∪ m2Chores := by
      calc
        (prefixChores ∪ ({first, second} : Finset Item)) ∪ (m2Chores \ {first, second}) =
            prefixChores ∪ (({first, second} : Finset Item) ∪ (m2Chores \ {first, second})) :=
          Finset.union_assoc _ _ _
        _ = prefixChores ∪ m2Chores := by rw [hgapResidueUnion]
    rw [← hgoods]
    exact hcombined
  refine ⟨fun agent => left agent ∪ right agent, hfinalAllocation, ?_⟩
  exact efx_union_of_short_unit_slack_and_controlled_exceptional_with_favorite Item r cost
    left right 0 1 (by decide) hbundlesDisjoint hcostLower
    (by simpa [left] using hleftShort) (by simpa [left] using hleftOther)
    (by simpa [left] using hleftToShort) hrightFavorite hunit hrightLarge hrightAway
    hrightComparison hspecialLeft

/-- The full fixed-label dispatcher for source Case B.4.2(a).  The residual
M₂ instance is split only on its two exceptional shapes; both resulting
allocations retain the original prefix and the two gap chores. -/
theorem existsEfxOfM01M2_b3_disjoint_shortEndpoint
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (htypes : ∀ item ∈ m2Chores,
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)))
    (hresidueCount : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet cost item = ({0, 1} : Finset (Fin 4))).card ≤
      ((m2Chores \ {first, second}).filter
        fun item => smallAgentSet cost item = ({2, 3} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second})
  · exact existsEfxOfM01M2_b3_disjoint_shortEndpoint_nonexceptional Item r cost
      prefixChores m2Chores a quota prefixAllocation first second hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond htypes hresidueCount hnotExceptional
  · exact existsEfxOfM01M2_b3_disjoint_shortEndpoint_exceptional Item r cost
      prefixChores m2Chores a quota prefixAllocation first second hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond htypes hresidueCount
      (not_not.mp hnotExceptional)

/-- The B.4.2(a) fixed-label dispatcher is stable under the source's final
M₃₄ insertion phase. -/
theorem existsEfxOfM01M2M34_b3_disjoint_shortEndpoint
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (htypes : ∀ item ∈ m2Chores,
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)))
    (hresidueCount : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet cost item = ({0, 1} : Finset (Fin 4))).card ≤
      ((m2Chores \ {first, second}).filter
        fun item => smallAgentSet cost item = ({2, 3} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEfx⟩ :=
    existsEfxOfM01M2_b3_disjoint_shortEndpoint Item r cost prefixChores m2Chores a quota
      prefixAllocation first second hr hcost hprefixM2 hcanonical hquota0 hquota1 hquota2
      hquota3 hsuper hfirst hsecond htypes hresidueCount
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEfx

/-- Relabelled entry point for B.4.2(a).  The caller supplies a matching
already named `(0,1),(2,3)` in working labels; the resulting EFX allocation
is transported back to the original agents. -/
theorem existsEfxOfM01M2_b3_disjoint_shortEndpoint_of_relabelled_types
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4)))
    (htypes : ∀ item ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet (relabelChoreCost labels cost) item = ({2, 3} : Finset (Fin 4)))
    (hresidueCount : ((m2Chores \ {first, second}).filter
      fun item => smallAgentSet (relabelChoreCost labels cost) item =
        ({0, 1} : Finset (Fin 4))).card ≤
      ((m2Chores \ {first, second}).filter
        fun item => smallAgentSet (relabelChoreCost labels cost) item =
          ({2, 3} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfM01M2_b3_disjoint_shortEndpoint Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a quota prefixAllocation first second hr
    (IsOneOrRChoreCost.relabel labels cost r hcost) hprefixM2 hcanonical hquota0 hquota1
    hquota2 hquota3 hsuper hfirst hsecond htypes hresidueCount

/-- The exceptional-residue classification in source Case B.4.2(b).  The M₂
pool has exactly the disjoint types `(0,1)` and `(2,3)`, with the latter at
least as frequent.  Removing one type-`(0,1)` chore leaves any exceptional
residue with auxiliary endpoints `(0,1)`. -/
theorem b3_disjoint_heavy_exceptional_auxiliary_pair
    (Item : Type) [DecidableEq Item] (cost : ChoreCost (Fin 4) Item)
    (m2Chores : Finset Item) (first second : Item)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (htypes : ∀ item ∈ m2Chores,
      smallAgentSet cost item = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost item = ({2, 3} : Finset (Fin 4)))
    (hcount : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card)
    (hexceptional : IsM2Exceptional cost (m2Chores \ {first})) :
    IsM2ExceptionalWithEndpoints cost (m2Chores \ {first}) 0 1 := by
  classical
  let residue : Finset Item := m2Chores \ {first}
  have htypesNe : ({0, 1} : Finset (Fin 4)) ≠ {2, 3} := by decide
  have hfirstNeSecond : first ≠ second := by
    intro heq
    subst second
    exact (Finset.disjoint_left.mp
      (m2TypeChorePool_disjoint_of_ne cost m2Chores
        ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) htypesNe) hfirst hsecond).elim
  have hsecondResidue : second ∈ residue := by
    refine Finset.mem_sdiff.mpr ⟨?_, by simpa using hfirstNeSecond.symm⟩
    exact (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) second).mp hsecond |>.1
  have hsecondSmall : smallAgentSet cost second = ({2, 3} : Finset (Fin 4)) :=
    (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) second).mp hsecond |>.2
  have hdominantLarge : ∀ dominant auxiliary : Finset (Fin 4), ∀ q : ℕ,
      dominant.card = 2 → auxiliary.card = 2 → Disjoint dominant auxiliary →
      (((∀ item ∈ residue, smallAgentSet cost item = dominant) ∧
          residue.card = 4 * q + 3) ∨
        (∃ exceptionalItem ∈ residue, smallAgentSet cost exceptionalItem = auxiliary ∧
          (∀ item ∈ residue.erase exceptionalItem, smallAgentSet cost item = dominant) ∧
          (residue.erase exceptionalItem).card = 4 * q + 3)) →
      3 ≤ (m2TypeChorePool cost m2Chores dominant).card := by
    intro dominant auxiliary q _hdominant _hauxiliary _hdisjoint hshape
    rcases hshape with hfixed | hsingle
    · have hsubset : residue ⊆ m2TypeChorePool cost m2Chores dominant := by
        intro item hitem
        have hitemBase : item ∈ m2Chores := by
          have hitem' : item ∈ m2Chores \ {first} := by simpa [residue] using hitem
          exact Finset.sdiff_subset hitem'
        exact (mem_m2TypeChorePool cost m2Chores dominant item).mpr
          ⟨hitemBase, hfixed.1 item hitem⟩
      have hcard := Finset.card_le_card hsubset
      rw [hfixed.2] at hcard
      omega
    · obtain ⟨exceptionalItem, _hexceptionalItem, _hitemType, houtsideType,
          houtsideCard⟩ := hsingle
      have hsubset : residue.erase exceptionalItem ⊆
          m2TypeChorePool cost m2Chores dominant := by
        intro item hitem
        exact (mem_m2TypeChorePool cost m2Chores dominant item).mpr
          ⟨Finset.sdiff_subset (Finset.erase_subset exceptionalItem residue hitem),
            houtsideType item hitem⟩
      have hcard := Finset.card_le_card hsubset
      rw [houtsideCard] at hcard
      omega
  rcases hexceptional with ⟨dominant, auxiliary, q, hdominant, hauxiliary,
      hdisjoint, hshape⟩
  have hauxiliaryOfDominant23
      (hdominantEq : dominant = ({2, 3} : Finset (Fin 4))) :
      auxiliary = ({0, 1} : Finset (Fin 4)) := by
    have hsubset : auxiliary ⊆ ({2, 3} : Finset (Fin 4))ᶜ := by
      intro agent hagent
      simp only [Finset.mem_compl]
      intro hdominantMem
      exact Finset.disjoint_left.mp hdisjoint (by simpa [hdominantEq] using hdominantMem)
        hagent
    have hauxiliaryCompl : auxiliary = ({2, 3} : Finset (Fin 4))ᶜ := by
      apply Finset.eq_of_subset_of_card_le hsubset
      have hcomplementCard : (({2, 3} : Finset (Fin 4))ᶜ).card = 2 := by decide
      rw [hcomplementCard, hauxiliary]
    calc
      auxiliary = ({2, 3} : Finset (Fin 4))ᶜ := hauxiliaryCompl
      _ = ({0, 1} : Finset (Fin 4)) := by decide
  have hauxiliaryEq : auxiliary = ({0, 1} : Finset (Fin 4)) := by
    rcases hshape with hfixed | hsingle
    · have hdominantEq : dominant = ({2, 3} : Finset (Fin 4)) :=
        (hfixed.1 second hsecondResidue).symm.trans hsecondSmall
      exact hauxiliaryOfDominant23 hdominantEq
    · obtain ⟨exceptionalItem, hexceptionalItem, hitemType, houtsideType,
        houtsideCard⟩ := hsingle
      by_cases hsecondExceptional : second = exceptionalItem
      · subst exceptionalItem
        have hdominantPoolLarge : 3 ≤ (m2TypeChorePool cost m2Chores dominant).card :=
          hdominantLarge dominant auxiliary q hdominant hauxiliary hdisjoint
            (Or.inr ⟨second, hsecondResidue, hitemType, houtsideType, houtsideCard⟩)
        have houtsidePos : 0 < (residue.erase second).card := by
          rw [houtsideCard]
          omega
        obtain ⟨outside, houtside⟩ := Finset.card_pos.mp houtsidePos
        have houtsideBase : outside ∈ m2Chores :=
          Finset.sdiff_subset (Finset.erase_subset second residue houtside)
        rcases htypes outside houtsideBase with houtside01 | houtside23
        · have hdominantEq : dominant = ({0, 1} : Finset (Fin 4)) :=
            (houtsideType outside houtside).symm.trans houtside01
          have hfirstPoolLarge : 3 ≤
              (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card := by
            simpa [hdominantEq] using hdominantPoolLarge
          have hsecondTypeSubset :
              m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) ⊆ {second} := by
            intro item hitem
            by_cases hitemSecond : item = second
            · simp [hitemSecond]
            · have hitemBase :=
                (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp
                  hitem |>.1
              have hitemNeFirst : item ≠ first := by
                intro heq
                subst item
                exact (Finset.disjoint_left.mp
                  (m2TypeChorePool_disjoint_of_ne cost m2Chores
                    ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) htypesNe)
                  hfirst hitem).elim
              have hitemResidue : item ∈ residue := by
                exact Finset.mem_sdiff.mpr ⟨hitemBase, by simpa using hitemNeFirst⟩
              have hitemOutside : item ∈ residue.erase second :=
                Finset.mem_erase.mpr ⟨hitemSecond, hitemResidue⟩
              have hitemDominant : smallAgentSet cost item = dominant :=
                houtsideType item hitemOutside
              have hitem23 : smallAgentSet cost item = ({2, 3} : Finset (Fin 4)) :=
                (mem_m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)) item).mp hitem |>.2
              exact (htypesNe (hdominantEq.symm.trans (hitemDominant.symm.trans hitem23))).elim
          have hsecondPoolSmall :
              (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card ≤ 1 := by
            calc
              (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card ≤
                  ({second} : Finset Item).card := Finset.card_le_card hsecondTypeSubset
              _ = 1 := by simp
          omega
        · have hdominantEq : dominant = ({2, 3} : Finset (Fin 4)) :=
            (houtsideType outside houtside).symm.trans houtside23
          have hauxiliary23 : auxiliary = ({2, 3} : Finset (Fin 4)) :=
            hitemType.symm.trans hsecondSmall
          exact (Finset.disjoint_left.mp hdisjoint
            (by simp [hdominantEq] : (2 : Fin 4) ∈ dominant)
            (by simp [hauxiliary23] : (2 : Fin 4) ∈ auxiliary)).elim
      · have hdominantEq : dominant = ({2, 3} : Finset (Fin 4)) :=
          ((houtsideType second
            (Finset.mem_erase.mpr ⟨hsecondExceptional, hsecondResidue⟩)).symm).trans
              hsecondSmall
        exact hauxiliaryOfDominant23 hdominantEq
  refine ⟨dominant, auxiliary, q, hdominant, hauxiliary, hdisjoint, ?_, ?_, hshape⟩
  · simp [hauxiliaryEq]
  · simp [hauxiliaryEq]

/-- Source Case B.4.2(b) after its residual classification.  The prefix
premises express the source condition that the `(0,1)` endpoints are heavy in
every super-canonical allocation; the two-type hypotheses make the displayed
one-item gap fill and exceptional route exhaustive. -/
theorem existsEfxOfM01M2_b3_disjoint_heavyEndpoints
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (htypes : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost chore = ({2, 3} : Finset (Fin 4)))
    (hcount : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card)
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {item})
  · exact existsEfxOfM01M2_b3_disjoint_heavyEndpoints_nonexceptional Item r cost
      prefixChores m2Chores a quota prefixAllocation item hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hitem hm2Small hprefixZeroSmall
      hprefixOneSmall hnotExceptional
  exact existsEfxOfM01M2_b3_disjoint_heavyEndpoints_exceptional Item r cost
    prefixChores m2Chores a quota prefixAllocation item hr hcost hprefixM2 hprefixSmall
    hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hitem hprefixZeroSmall hprefixOneSmall
    (b3_disjoint_heavy_exceptional_auxiliary_pair Item cost m2Chores item second hitem hsecond
      htypes hcount (not_not.mp hnotExceptional))

/-- The complete fixed-label B.4.2(b) dispatcher extends through every M₃₄
chore by the source insertion lemma. -/
theorem existsEfxOfM01M2M34_b3_disjoint_heavyEndpoints
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm34Small : ∀ chore ∈ m34Chores, IsSmallForAtLeastThree cost chore)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4)))
    (htypes : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet cost chore = ({2, 3} : Finset (Fin 4)))
    (hcount : (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool cost m2Chores ({2, 3} : Finset (Fin 4))).card)
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEfx⟩ :=
    existsEfxOfM01M2_b3_disjoint_heavyEndpoints Item r cost prefixChores m2Chores a quota
      prefixAllocation item second hr hcost hprefixM2 hprefixSmall hcanonical hquota0 hquota1
      hquota2 hquota3 hsuper hitem hsecond hm2Small htypes hcount hprefixZeroSmall
      hprefixOneSmall
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEfx

/-- Source Case B.4.1(a), including its complete exceptional-residue
dispatch.  The M₀₁ prefix has agent `0` as its unique short agent and is
super-canonical; the two displayed intersecting M₂ fibres provide the two
gap-filling chores. -/
theorem existsEfxOfM01M2_b3_intersecting_supercanonical
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hnotExceptional : ¬ IsM2Exceptional cost (m2Chores \ {first, second})
  · exact existsEfxOfM01M2_b3_intersecting_nonexceptional Item r cost prefixChores
      m2Chores a quota prefixAllocation first second hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond hm2Small hnotExceptional
  obtain ⟨exceptionalI, exceptionalJ, hij, hexceptional⟩ :=
    exists_ordered_exceptional_endpoints Item cost (m2Chores \ {first, second})
      (not_not.mp hnotExceptional)
  by_cases hIzero : exceptionalI = 0
  · subst exceptionalI
    exact existsEfxOfM01M2_b3_intersecting_exceptional_with_short Item r cost
      prefixChores m2Chores a quota prefixAllocation first second hr hcost hprefixM2
      hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond exceptionalJ
      (IsM2ExceptionalWithEndpoints.swap Item cost (m2Chores \ {first, second})
        0 exceptionalJ hexceptional) (Ne.symm hij)
  by_cases hJzero : exceptionalJ = 0
  · subst exceptionalJ
    exact existsEfxOfM01M2_b3_intersecting_exceptional_with_short Item r cost
      prefixChores m2Chores a quota prefixAllocation first second hr hcost hprefixM2
      hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond exceptionalI
      hexceptional hIzero
  · exact existsEfxOfM01M2_b3_intersecting_exceptional_away_short Item r cost
      prefixChores m2Chores a quota prefixAllocation first second hr hcost hprefixM2
      hprefixSmall hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond
      exceptionalI exceptionalJ hexceptional hij hIzero hJzero

/-- The B.4.1(a) dispatcher is stable under the final M₃₄ insertion phase.
This is the source's global postprocessing step, stated here for the complete
intersecting-super-canonical subcase. -/
theorem existsEfxOfM01M2M34_b3_intersecting_supercanonical
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm2Small : ∀ item ∈ m2Chores, IsSmallForExactlyTwo cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEfx⟩ :=
    existsEfxOfM01M2_b3_intersecting_supercanonical Item r cost prefixChores m2Chores
      a quota prefixAllocation first second hr hcost hprefixM2 hprefixSmall hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond hm2Small
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEfx

/-- The full fixed-label dispatcher for source Case B.4.1.  A canonical
prefix with the common endpoint `0` short is selected directly.  If it is
super-canonical the two-chore gap fill applies; otherwise the B.4.1(b) prefix
switch and global-maximum residual classification apply. -/
theorem existsEfxOfM01M2_b3_intersectingMaximum
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let quota : Fin 4 → ℕ := canonicalQuota a (Finset.univ \ {0})
  have hlongCard : (Finset.univ \ ({0} : Finset (Fin 4))).card = 3 := by decide
  have hquotaSum : Finset.univ.sum quota = prefixChores.card := by
    rw [show quota = canonicalQuota a (Finset.univ \ {0}) by rfl, canonicalQuota_sum,
      hlongCard, hprefixCard]
  obtain ⟨prefixAllocation, hcanonical⟩ :=
    existsCanonicalSmallChoreAllocation Item cost prefixChores quota hquotaSum hprefixSmall
  have hquota0 : quota 0 = a := by simp [quota, canonicalQuota]
  have hquota1 : quota 1 = a + 1 := by simp [quota, canonicalQuota]
  have hquota2 : quota 2 = a + 1 := by simp [quota, canonicalQuota]
  have hquota3 : quota 3 = a + 1 := by simp [quota, canonicalQuota]
  by_cases hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r
  · exact existsEfxOfM01M2_b3_intersecting_supercanonical Item r cost prefixChores
      m2Chores a quota prefixAllocation first second hr hcost hprefixM2 hprefixSmall
      hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hfirst hsecond hm2Small
  · exact existsEfxOfM01M2_b3_intersecting_nonsupercanonical_of_maximum Item r cost
      prefixChores m2Chores a quota prefixAllocation first hr hcost hprefixM2 hprefixCard
      hprefixSmall hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hfirst second hsecond
      hm2Small hmaximum

/-- Case B.4.1 remains closed under the source's final iterated M₃₄ insertion
phase. -/
theorem existsEfxOfM01M2M34_b3_intersectingMaximum
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ) (first second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores)
    (hprefixCard : prefixChores.card = 4 * a + 3)
    (hprefixSmall : ∀ chore ∈ prefixChores, IsSmallForAtMostOne cost chore)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm34Small : ∀ chore ∈ m34Chores, IsSmallForAtLeastThree cost chore)
    (hfirst : first ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool cost m2Chores ({0, 2} : Finset (Fin 4)))
    (hmaximum : ∀ edgeType : Finset (Fin 4),
      (m2TypeChorePool cost m2Chores edgeType).card ≤
        (m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4))).card) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEfx⟩ :=
    existsEfxOfM01M2_b3_intersectingMaximum Item r cost prefixChores m2Chores a first
      second hr hcost hprefixM2 hprefixCard hprefixSmall hm2Small hfirst hsecond hmaximum
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEfx

/-- Relabelled entry point for B.4.2(b).  The caller names the two matching
types `(0,1)` and `(2,3)` in working labels, with the heavy endpoints in the
first type and the short prefix endpoint named `3`; the EFX allocation is then
transported back to the original agent labels. -/
theorem existsEfxOfM01M2_b3_disjoint_heavyEndpoints_of_relabelled_types
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (item second : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ chore ∈ prefixChores,
      IsSmallForAtMostOne (relabelChoreCost labels cost) chore)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hsecond : second ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({2, 3} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores,
      IsSmallForExactlyTwo (relabelChoreCost labels cost) chore)
    (htypes : ∀ chore ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4)) ∨
        smallAgentSet (relabelChoreCost labels cost) chore = ({2, 3} : Finset (Fin 4)))
    (hcount : (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4))).card ≤
      (m2TypeChorePool (relabelChoreCost labels cost) m2Chores
        ({2, 3} : Finset (Fin 4))).card)
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0,
      IsSmallChore (relabelChoreCost labels cost) 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1,
      IsSmallChore (relabelChoreCost labels cost) 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfM01M2_b3_disjoint_heavyEndpoints Item r
    (relabelChoreCost labels cost) prefixChores m2Chores a quota prefixAllocation item second
    hr (IsOneOrRChoreCost.relabel labels cost r hcost) hprefixM2 hprefixSmall hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hitem hsecond hm2Small htypes hcount
    hprefixZeroSmall hprefixOneSmall

/-- Source Case B.4.3(a), with its complete cardinality dispatcher.  When the
fixed type pool has at most `r` chores it is all gap-filled; otherwise the
source removes `⌊r⌋₊` chores and the residual cardinality selects either the
ordinary round-robin composition (remainders `0,1,2`) or the controlled
remainder-three schedule. -/
theorem existsEfxOfM01M2_b3_oneType_shortEndpoint
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  by_cases hsmallPool : (m2Chores.card : ℝ) ≤ r
  · exact existsEfxOfM01M2_b3_oneType_shortEndpoint_smallPool Item r cost
      prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hm2Type hsmallPool
  have hlargePool : r < (m2Chores.card : ℝ) := lt_of_not_ge hsmallPool
  by_cases hnonexceptional : (m2Chores.card - ⌊r⌋₊) % 4 < 3
  · exact existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_nonexceptional_of_card_gt
      Item r cost prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2
      hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hm2Type hlargePool hnonexceptional
  have hremainderBound : (m2Chores.card - ⌊r⌋₊) % 4 < 4 := Nat.mod_lt _ (by omega)
  have hthree : (m2Chores.card - ⌊r⌋₊) % 4 = 3 := by omega
  exact existsEfxOfM01M2_b3_oneType_shortEndpoint_largePool_exceptional_of_card_gt
    Item r cost prefixChores m2Chores a quota prefixAllocation hr hcost hprefixM2
    hprefixSmall hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hm2Type hlargePool hthree

/-- The complete one-type short-endpoint branch also extends through all
M₃₄ chores by the paper's iterated insertion lemma. -/
theorem existsEfxOfM01M2M34_b3_oneType_shortEndpoint
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores)
    (hprefixSmall : ∀ item ∈ prefixChores, IsSmallForAtMostOne cost item)
    (hm34Small : ∀ item ∈ m34Chores, IsSmallForAtLeastThree cost item)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEfx⟩ :=
    existsEfxOfM01M2_b3_oneType_shortEndpoint Item r cost prefixChores m2Chores a quota
      prefixAllocation hr hcost hprefixM2 hprefixSmall hcanonical hquota0 hquota1 hquota2
      hquota3 hsuper hm2Type
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEfx

/-- Source Case B.4.3(b), with the fixed-type residual dispatched by its
actual remainder modulo four.  After the one type-`(0,1)` gap chore is
removed, remainders `0,1,2` use the ordinary certificate, while remainder
`3` is exactly the exceptional residue with auxiliary endpoints `(2,3)`. -/
theorem existsEfxOfM01M2_b3_oneType_heavyEndpoints
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  let residueChores : Finset Item := m2Chores \ {item}
  let residueQ : ℕ := residueChores.card / 4
  let residueRemainder : ℕ := residueChores.card % 4
  have hitemM2 : item ∈ m2Chores :=
    (mem_m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)) item).mp hitem |>.1
  have hresidueCardNat : residueChores.card = m2Chores.card - 1 := by
    rw [show residueChores = m2Chores \ {item} by rfl,
      Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hitemM2]
  have hresidueCard : residueChores.card = 4 * residueQ + residueRemainder := by
    dsimp [residueQ, residueRemainder]
    have hmod := Nat.mod_add_div residueChores.card 4
    omega
  have hresidueRemainder : residueRemainder < 4 := by
    dsimp [residueRemainder]
    exact Nat.mod_lt _ (by omega)
  have hresidueType : ∀ chore ∈ residueChores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)) := by
    intro chore hchore
    have hchore' : chore ∈ m2Chores \ {item} := by
      simpa [residueChores] using hchore
    exact hm2Type chore (Finset.sdiff_subset hchore')
  by_cases hthree : residueRemainder = 3
  · have hexceptional : IsM2ExceptionalWithEndpoints cost residueChores 2 3 := by
      refine ⟨({0, 1} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), residueQ,
        by decide, by decide, by decide, by simp, by simp, Or.inl ?_⟩
      exact ⟨hresidueType, hresidueCard.trans (by simp [hthree])⟩
    exact existsEfxOfM01M2_b3_oneType_heavyEndpoints_exceptional Item r cost
      prefixChores m2Chores a quota prefixAllocation item hr hcost hprefixM2 hcanonical
      hquota0 hquota1 hquota2 hquota3 hsuper hitem hprefixZeroSmall hprefixOneSmall
      (by simpa [residueChores] using hexceptional)
  · exact existsEfxOfM01M2_b3_oneType_heavyEndpoints_nonexceptional Item r cost
      prefixChores m2Chores a quota prefixAllocation item residueQ residueRemainder hr hcost
      hprefixM2 hcanonical hquota0 hquota1 hquota2 hquota3 hsuper hitem hm2Small hm2Type
      (by simpa [residueChores] using hresidueCard) hresidueRemainder hthree
      hprefixZeroSmall hprefixOneSmall

/-- The full fixed-type heavy-endpoint branch is also closed under the final
M₃₄ insertion step. -/
theorem existsEfxOfM01M2M34_b3_oneType_heavyEndpoints
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (prefixChores m2Chores m34Chores : Finset Item) (a : ℕ) (quota : Fin 4 → ℕ)
    (prefixAllocation : Allocation (Fin 4) Item) (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hbaseM34 : Disjoint (prefixChores ∪ m2Chores) m34Chores)
    (hm2Small : ∀ chore ∈ m2Chores, IsSmallForExactlyTwo cost chore)
    (hm34Small : ∀ chore ∈ m34Chores, IsSmallForAtLeastThree cost chore)
    (hcanonical : IsCanonicalSmallChoreAllocation cost prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost cost own (prefixAllocation own) ≤
        additiveChoreCost cost own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool cost m2Chores ({0, 1} : Finset (Fin 4)))
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet cost chore = ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0, IsSmallChore cost 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1, IsSmallChore cost 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation ((prefixChores ∪ m2Chores) ∪ m34Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  obtain ⟨baseAllocation, hbaseAllocation, hbaseEfx⟩ :=
    existsEfxOfM01M2_b3_oneType_heavyEndpoints Item r cost prefixChores m2Chores a
      quota prefixAllocation item hr hcost hprefixM2 hcanonical hquota0
      hquota1 hquota2 hquota3 hsuper hitem hm2Small hm2Type hprefixZeroSmall hprefixOneSmall
  exact extendEfxByM34 Item r cost (prefixChores ∪ m2Chores) m34Chores hr hcost
    hbaseM34 hm34Small baseAllocation hbaseAllocation hbaseEfx

/-- Relabelled entry point for the short-endpoint half of B.4.3.  The unique
M₂ type is `(0,1)` in working labels and agent `0` is the super-canonical
short endpoint. -/
theorem existsEfxOfM01M2_b3_oneType_shortEndpoint_of_relabelled_type
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hprefixSmall : ∀ chore ∈ prefixChores,
      IsSmallForAtMostOne (relabelChoreCost labels cost) chore)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a + 1)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation comparison) - r)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4))) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfM01M2_b3_oneType_shortEndpoint Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a quota prefixAllocation hr
    (IsOneOrRChoreCost.relabel labels cost r hcost) hprefixM2 hprefixSmall hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hm2Type

/-- Relabelled entry point for the heavy-endpoint half of B.4.3.  The working
labels retain the unique M₂ type `(0,1)`, name its two heavy endpoints `0,1`,
and put the selected short endpoint at `3`. -/
theorem existsEfxOfM01M2_b3_oneType_heavyEndpoints_of_relabelled_type
    (Item : Type) [DecidableEq Item] (r : ℝ) (cost : ChoreCost (Fin 4) Item)
    (labels : Fin 4 ≃ Fin 4) (prefixChores m2Chores : Finset Item)
    (a : ℕ) (quota : Fin 4 → ℕ) (prefixAllocation : Allocation (Fin 4) Item)
    (item : Item)
    (hr : 2 < r) (hcost : IsOneOrRChoreCost cost r)
    (hprefixM2 : Disjoint prefixChores m2Chores)
    (hcanonical : IsCanonicalSmallChoreAllocation (relabelChoreCost labels cost)
      prefixChores quota prefixAllocation)
    (hquota0 : quota 0 = a + 1) (hquota1 : quota 1 = a + 1)
    (hquota2 : quota 2 = a + 1) (hquota3 : quota 3 = a)
    (hsuper : ∀ own comparison, quota own = a → quota comparison = a + 1 →
      additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation own) ≤
        additiveChoreCost (relabelChoreCost labels cost) own (prefixAllocation comparison) - r)
    (hitem : item ∈ m2TypeChorePool (relabelChoreCost labels cost) m2Chores
      ({0, 1} : Finset (Fin 4)))
    (hm2Small : ∀ chore ∈ m2Chores,
      IsSmallForExactlyTwo (relabelChoreCost labels cost) chore)
    (hm2Type : ∀ chore ∈ m2Chores,
      smallAgentSet (relabelChoreCost labels cost) chore = ({0, 1} : Finset (Fin 4)))
    (hprefixZeroSmall : ∀ chore ∈ prefixAllocation 0,
      IsSmallChore (relabelChoreCost labels cost) 0 chore)
    (hprefixOneSmall : ∀ chore ∈ prefixAllocation 1,
      IsSmallChore (relabelChoreCost labels cost) 1 chore) :
    ∃ allocation : Allocation (Fin 4) Item,
      IsAllocationOf allocation (prefixChores ∪ m2Chores) ∧
        EFXForChores (additiveChoreCost cost) allocation := by
  apply exists_efx_relabel_back labels cost (prefixChores ∪ m2Chores)
  exact existsEfxOfM01M2_b3_oneType_heavyEndpoints Item r (relabelChoreCost labels cost)
    prefixChores m2Chores a quota prefixAllocation item
    hr (IsOneOrRChoreCost.relabel labels cost r hcost) hprefixM2 hcanonical
    hquota0 hquota1 hquota2 hquota3 hsuper hitem hm2Small hm2Type
    hprefixZeroSmall hprefixOneSmall

end HT26EFXChores
