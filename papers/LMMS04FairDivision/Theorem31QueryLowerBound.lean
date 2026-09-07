import AppliedModelingLib.SocialChoice.FairDivision.Mechanisms
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem31

/-! ## Source hard family -/

/-- The two-player source hard instances in LMMS Theorem 3.1. -/
abbrev LMMS31Agent := Fin 2

/-- Raw reported bundle values for the two-player source hard instances. -/
abbrev LMMS31Report (Item : Type*) :=
  FairDivisionReport LMMS31Agent Item

/--
The hard utility functions used in the source proof for `m = 2k` goods.  The
paper specifies their values below, above, and on the middle layer of the
Boolean lattice, with complements on the middle layer summing to one.
-/
structure LMMS31HardFunction
    (Item : Type*) [Fintype Item] [DecidableEq Item] (k : ℕ) where
  val : Finset Item → ℝ
  zero_of_card_lt : ∀ S : Finset Item, S.card < k → val S = 0
  one_of_card_gt : ∀ S : Finset Item, k < S.card → val S = 1
  complement_sum_of_card_eq :
    ∀ S : Finset Item, S.card = k →
      val S + val ((Finset.univ : Finset Item) \ S) = 1
  binary_of_card_eq :
    ∀ S : Finset Item, S.card = k → val S = 0 ∨ val S = 1

/-- The crossed two-player report `(u,v)` from the source proof. -/
noncomputable def lmms31CrossReport
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (u v : LMMS31HardFunction Item k) : LMMS31Report Item :=
  fun p S => if p = (0 : LMMS31Agent) then u.val S else v.val S

@[simp] theorem lmms31CrossReport_zero
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (u v : LMMS31HardFunction Item k) (S : Finset Item) :
    lmms31CrossReport u v (0 : LMMS31Agent) S = u.val S := by
  simp [lmms31CrossReport]

@[simp] theorem lmms31CrossReport_one
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (u v : LMMS31HardFunction Item k) (S : Finset Item) :
    lmms31CrossReport u v (1 : LMMS31Agent) S = v.val S := by
  simp [lmms31CrossReport]

/-- The two-player allocation giving `S` to player 0 and its complement to player 1. -/
def lmms31TwoPlayerAllocation
    {Item : Type*} [Fintype Item] [DecidableEq Item] (S : Finset Item) :
    Allocation LMMS31Agent Item :=
  fun p => if p = (0 : LMMS31Agent) then S else Sᶜ

@[simp] theorem lmms31TwoPlayerAllocation_zero
    {Item : Type*} [Fintype Item] [DecidableEq Item] (S : Finset Item) :
    lmms31TwoPlayerAllocation S (0 : LMMS31Agent) = S := by
  simp [lmms31TwoPlayerAllocation]

@[simp] theorem lmms31TwoPlayerAllocation_one
    {Item : Type*} [Fintype Item] [DecidableEq Item] (S : Finset Item) :
    lmms31TwoPlayerAllocation S (1 : LMMS31Agent) = Sᶜ := by
  simp [lmms31TwoPlayerAllocation]

theorem lmms31TwoPlayerAllocation_isAllocationOf_univ
    {Item : Type*} [Fintype Item] [DecidableEq Item] (S : Finset Item) :
    IsAllocationOf
      (lmms31TwoPlayerAllocation S)
      (Finset.univ : Finset Item) := by
  classical
  constructor
  · intro i g hg
    simp
  · intro g hg
    by_cases hS : g ∈ S
    · refine ⟨(0 : LMMS31Agent), ?_, ?_⟩
      · simpa [lmms31TwoPlayerAllocation, hS]
      · intro i hi
        fin_cases i
        · rfl
        · simp [lmms31TwoPlayerAllocation, hS] at hi
    · refine ⟨(1 : LMMS31Agent), ?_, ?_⟩
      · simp [lmms31TwoPlayerAllocation, hS]
      · intro i hi
        fin_cases i
        · simp [lmms31TwoPlayerAllocation, hS] at hi
        · rfl

theorem lmms31_allocation_one_eq_compl_zero
    {Item : Type*} [Fintype Item] [DecidableEq Item]
    {A : Allocation LMMS31Agent Item}
    (halloc : IsAllocationOf A (Finset.univ : Finset Item)) :
    A (1 : LMMS31Agent) = (A (0 : LMMS31Agent))ᶜ := by
  classical
  ext g
  constructor
  · intro hg1
    simp only [Finset.mem_compl]
    intro hg0
    have hgoods : g ∈ (Finset.univ : Finset Item) := by simp
    have hsame :
        (0 : LMMS31Agent) = (1 : LMMS31Agent) :=
      isAllocationOf_owner_unique halloc hgoods hg0 hg1
    exact (by decide : (0 : LMMS31Agent) ≠ (1 : LMMS31Agent)) hsame
  · intro hg0
    have hg0_not : g ∉ A (0 : LMMS31Agent) := by
      simpa using hg0
    have hgoods : g ∈ (Finset.univ : Finset Item) := by simp
    obtain ⟨i, hi⟩ := isAllocationOf_exists_owner
      (A := A) (goods := (Finset.univ : Finset Item)) halloc hgoods
    fin_cases i
    · exact False.elim (hg0_not hi)
    · simpa using hi

/--
If two source hard functions disagree on a middle-layer set, then the crossed
instance `(u,v)` has an envy-free allocation: give that set to player 0 and
its complement to player 1.
-/
theorem lmms31_exists_envyFree_cross_of_middle_disagreement
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (u v : LMMS31HardFunction Item k)
    (hdisagree : ∃ S : Finset Item, S.card = k ∧ u.val S = 1 ∧ v.val S = 0) :
    ∃ A : Allocation LMMS31Agent Item,
      IsAllocationOf A (Finset.univ : Finset Item) ∧
        ReportEnvyFree (lmms31CrossReport u v) A := by
  classical
  rcases hdisagree with ⟨S, hScard, huS, hvS⟩
  refine
    ⟨lmms31TwoPlayerAllocation S,
      lmms31TwoPlayerAllocation_isAllocationOf_univ S, ?_⟩
  have huComp : u.val (Sᶜ) = 0 := by
    have hsum := u.complement_sum_of_card_eq S hScard
    have hsum' : u.val S + u.val Sᶜ = 1 := by
      simpa [Finset.compl_eq_univ_sdiff] using hsum
    linarith
  have hvComp : v.val (Sᶜ) = 1 := by
    have hsum := v.complement_sum_of_card_eq S hScard
    have hsum' : v.val S + v.val Sᶜ = 1 := by
      simpa [Finset.compl_eq_univ_sdiff] using hsum
    linarith
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lmms31CrossReport, lmms31TwoPlayerAllocation, huS, hvS, huComp, hvComp]

/--
If `u` is one and `v` is zero on a middle-layer set, then by complement
symmetry `v` is one and `u` is zero on the complementary middle-layer set.
Thus the swapped crossed instance `(v,u)` also has an envy-free allocation.
-/
theorem lmms31_exists_envyFree_swap_cross_of_middle_disagreement
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (u v : LMMS31HardFunction Item k)
    (hdisagree : ∃ S : Finset Item, S.card = k ∧ u.val S = 1 ∧ v.val S = 0) :
    ∃ A : Allocation LMMS31Agent Item,
      IsAllocationOf A (Finset.univ : Finset Item) ∧
        ReportEnvyFree (lmms31CrossReport v u) A := by
  classical
  rcases hdisagree with ⟨S, hScard, huS, hvS⟩
  have hcomp_card : Sᶜ.card = k := by
    rw [Finset.card_compl, hcard_items, hScard]
    omega
  have huComp : u.val (Sᶜ) = 0 := by
    have hsum := u.complement_sum_of_card_eq S hScard
    have hsum' : u.val S + u.val Sᶜ = 1 := by
      simpa [Finset.compl_eq_univ_sdiff] using hsum
    linarith
  have hvComp : v.val (Sᶜ) = 1 := by
    have hsum := v.complement_sum_of_card_eq S hScard
    have hsum' : v.val S + v.val Sᶜ = 1 := by
      simpa [Finset.compl_eq_univ_sdiff] using hsum
    linarith
  exact
    lmms31_exists_envyFree_cross_of_middle_disagreement
      v u ⟨Sᶜ, hcomp_card, hvComp, huComp⟩

/--
No allocation of all goods can be envy-free for both swapped crossed
instances `(u,v)` and `(v,u)` when the number of goods is `2k`.
-/
theorem lmms31_no_common_envyFree_cross_swap
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (u v : LMMS31HardFunction Item k) :
    ∀ A : Allocation LMMS31Agent Item,
      IsAllocationOf A (Finset.univ : Finset Item) →
        ¬ (ReportEnvyFree (lmms31CrossReport u v) A ∧
          ReportEnvyFree (lmms31CrossReport v u) A) := by
  classical
  intro A halloc hboth
  have hA1 : A (1 : LMMS31Agent) = (A (0 : LMMS31Agent))ᶜ :=
    lmms31_allocation_one_eq_compl_zero halloc
  have hA1card :
      (A (1 : LMMS31Agent)).card =
        2 * k - (A (0 : LMMS31Agent)).card := by
    rw [hA1, Finset.card_compl, hcard_items]
  have hu10 : u.val (A (1 : LMMS31Agent)) ≤ u.val (A (0 : LMMS31Agent)) := by
    simpa [lmms31CrossReport] using
      hboth.1 (0 : LMMS31Agent) (1 : LMMS31Agent)
  have hu01 : u.val (A (0 : LMMS31Agent)) ≤ u.val (A (1 : LMMS31Agent)) := by
    simpa [lmms31CrossReport] using
      hboth.2 (1 : LMMS31Agent) (0 : LMMS31Agent)
  rcases lt_trichotomy (A (0 : LMMS31Agent)).card k with hlt | heq | hgt
  · have hA1gt : k < (A (1 : LMMS31Agent)).card := by omega
    have hu0 : u.val (A (0 : LMMS31Agent)) = 0 :=
      u.zero_of_card_lt (A (0 : LMMS31Agent)) hlt
    have hu1 : u.val (A (1 : LMMS31Agent)) = 1 :=
      u.one_of_card_gt (A (1 : LMMS31Agent)) hA1gt
    linarith
  · have hsum :
        u.val (A (0 : LMMS31Agent)) +
          u.val (A (1 : LMMS31Agent)) = 1 := by
      simpa [hA1] using
        u.complement_sum_of_card_eq (A (0 : LMMS31Agent)) heq
    have hueq :
        u.val (A (0 : LMMS31Agent)) =
          u.val (A (1 : LMMS31Agent)) :=
      le_antisymm hu01 hu10
    rcases u.binary_of_card_eq (A (0 : LMMS31Agent)) heq with hu0 | hu1
    · linarith
    · linarith
  · have hA1lt : (A (1 : LMMS31Agent)).card < k := by
      have hA0le :
          (A (0 : LMMS31Agent)).card ≤ 2 * k := by
        rw [← hcard_items]
        exact Finset.card_le_univ (A (0 : LMMS31Agent))
      omega
    have hu0 : u.val (A (0 : LMMS31Agent)) = 1 :=
      u.one_of_card_gt (A (0 : LMMS31Agent)) hgt
    have hu1 : u.val (A (1 : LMMS31Agent)) = 0 :=
      u.zero_of_card_lt (A (1 : LMMS31Agent)) hA1lt
    linarith

/-- The two swapped crossed instances used in the source proof. -/
noncomputable def lmms31SwappedCrossReport
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (u v : LMMS31HardFunction Item k) :
    LMMS31Agent → LMMS31Report Item :=
  fun inst =>
    if inst = (0 : LMMS31Agent) then lmms31CrossReport u v
    else lmms31CrossReport v u

@[simp] theorem lmms31SwappedCrossReport_zero
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (u v : LMMS31HardFunction Item k) :
    lmms31SwappedCrossReport u v (0 : LMMS31Agent) =
      lmms31CrossReport u v := by
  simp [lmms31SwappedCrossReport]

@[simp] theorem lmms31SwappedCrossReport_one
    {Item : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (u v : LMMS31HardFunction Item k) :
    lmms31SwappedCrossReport u v (1 : LMMS31Agent) =
      lmms31CrossReport v u := by
  simp [lmms31SwappedCrossReport]

/--
Concrete swapped-pair minimum-envy obstruction for Theorem 3.1.  If the
deterministic transcript is the same on `(u,v)` and `(v,u)`, then the same
output allocation cannot be minimum-envy for both source profiles.
-/
theorem lmms31_minimum_envy_query_lower_bound_of_swapped_cross_pair
    {Item Transcript : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (u v : LMMS31HardFunction Item k)
    (hdisagree :
      ∃ S : Finset Item, S.card = k ∧ u.val S = 1 ∧ v.val S = 0)
    (transcript : LMMS31Agent → Transcript)
    (output : Transcript → Allocation LMMS31Agent Item)
    (htranscript :
      transcript (0 : LMMS31Agent) = transcript (1 : LMMS31Agent)) :
    ¬ ∀ inst : LMMS31Agent,
      MinimumReportEnvyAllocation
        (lmms31SwappedCrossReport u v inst)
        (Finset.univ : Finset Item)
        (output (transcript inst)) := by
  classical
  intro hcorrect
  let A : Allocation LMMS31Agent Item := output (transcript (0 : LMMS31Agent))
  have hleft :
      MinimumReportEnvyAllocation
        (lmms31CrossReport u v)
        (Finset.univ : Finset Item) A := by
    simpa [A] using hcorrect (0 : LMMS31Agent)
  have hright :
      MinimumReportEnvyAllocation
        (lmms31CrossReport v u)
        (Finset.univ : Finset Item) A := by
    simpa [A, htranscript] using hcorrect (1 : LMMS31Agent)
  have hfree_left :
      ReportEnvyFree (lmms31CrossReport u v) A := by
    have hexists :=
      lmms31_exists_envyFree_cross_of_middle_disagreement u v hdisagree
    have hfree :=
      reportEnvyFree_of_minimumReportEnvyAllocation_of_exists
        hleft hexists
    simpa using hfree
  have hfree_right :
      ReportEnvyFree (lmms31CrossReport v u) A := by
    have hexists :=
      lmms31_exists_envyFree_swap_cross_of_middle_disagreement
        hcard_items u v hdisagree
    have hfree :=
      reportEnvyFree_of_minimumReportEnvyAllocation_of_exists
        hright hexists
    simpa using hfree
  exact
    lmms31_no_common_envyFree_cross_swap
      hcard_items u v A hleft.1 ⟨hfree_left, hfree_right⟩

/-!
# Deterministic Query Lower-Bound Core for LMMS Theorem 3.1

The source proof of Theorem 3.1 uses a pigeonhole step: if a deterministic
algorithm has fewer possible query transcripts than hard instances, then two
distinct instances have the same transcript.  If no single output can be
optimal for both of those indistinguishable instances, the algorithm cannot be
correct on all instances.

This file formalizes that generic deterministic-query core.  The concrete
LMMS hard valuation family and transcript-count estimates remain separate
source obligations.
-/

/--
If a finite map goes from a larger type to a smaller type, two distinct inputs
collide.
-/
theorem exists_collision_of_card_lt
    {Instance Transcript : Type*} [Fintype Instance] [Fintype Transcript]
    (transcript : Instance → Transcript)
    (hcard : Fintype.card Transcript < Fintype.card Instance) :
    ∃ i j : Instance, i ≠ j ∧ transcript i = transcript j := by
  classical
  by_contra hno
  push Not at hno
  have hinj : Function.Injective transcript := by
    intro i j hij
    by_contra hne
    exact hno i j hne hij
  have hle : Fintype.card Instance ≤ Fintype.card Transcript :=
    Fintype.card_le_of_injective transcript hinj
  exact not_lt_of_ge hle hcard

/--
Generic deterministic-query lower-bound certificate.

An algorithm is represented by a transcript map and an output chosen from the
transcript.  If there are fewer transcripts than hard instances, and any two
distinct instances with the same transcript have no common optimal output, then
the algorithm is not correct on all instances.
-/
theorem deterministic_query_lower_bound_of_no_common_optimal
    {Instance Transcript Output : Type*}
    [Fintype Instance] [Fintype Transcript]
    (transcript : Instance → Transcript)
    (output : Transcript → Output)
    (Optimal : Instance → Output → Prop)
    (hcard : Fintype.card Transcript < Fintype.card Instance)
    (hnoCommon :
      ∀ i j : Instance, i ≠ j → transcript i = transcript j →
        ∀ out : Output, ¬ (Optimal i out ∧ Optimal j out)) :
    ¬ ∀ i : Instance, Optimal i (output (transcript i)) := by
  classical
  intro hcorrect
  rcases exists_collision_of_card_lt transcript hcard with
    ⟨i, j, hij_ne, hij_transcript⟩
  have hi : Optimal i (output (transcript i)) := hcorrect i
  have hj : Optimal j (output (transcript i)) := by
    simpa [hij_transcript] using hcorrect j
  exact hnoCommon i j hij_ne hij_transcript (output (transcript i)) ⟨hi, hj⟩

/--
The last step of the source proof: if two hard instances are
indistinguishable to a deterministic algorithm, but no single output is optimal
for both, then the algorithm cannot be correct on all instances.
-/
theorem deterministic_query_lower_bound_of_indistinguishable_pair
    {Instance Transcript Output : Type*}
    (transcript : Instance → Transcript)
    (output : Transcript → Output)
    (Optimal : Instance → Output → Prop)
    {i j : Instance}
    (htranscript : transcript i = transcript j)
    (hnoCommon : ∀ out : Output, ¬ (Optimal i out ∧ Optimal j out)) :
    ¬ ∀ inst : Instance, Optimal inst (output (transcript inst)) := by
  intro hcorrect
  have hi : Optimal i (output (transcript i)) := hcorrect i
  have hj : Optimal j (output (transcript i)) := by
    simpa [htranscript] using hcorrect j
  exact hnoCommon (output (transcript i)) ⟨hi, hj⟩

/--
Certificate form for the indistinguishable-pair step.  The paper applies this
after the counting argument has produced two source functions whose swapped
two-player instances generate the same query transcript.
-/
structure IndistinguishablePairCertificate
    (Instance Transcript Output : Type*) where
  left : Instance
  right : Instance
  transcript : Instance → Transcript
  output : Transcript → Output
  Optimal : Instance → Output → Prop
  sameTranscript : transcript left = transcript right
  noCommonOptimal :
    ∀ out : Output, ¬ (Optimal left out ∧ Optimal right out)

theorem IndistinguishablePairCertificate.not_correct
    {Instance Transcript Output : Type*}
    (C : IndistinguishablePairCertificate Instance Transcript Output) :
    ¬ ∀ inst : Instance, C.Optimal inst (C.output (C.transcript inst)) :=
  deterministic_query_lower_bound_of_indistinguishable_pair
    C.transcript C.output C.Optimal C.sameTranscript C.noCommonOptimal

/--
Swapped-profile form matching the displayed `(u,v)` and `(v,u)` instances in
the source proof of Theorem 3.1.
-/
theorem deterministic_query_lower_bound_of_swapped_indistinguishable_pair
    {Valuation Transcript Output : Type*}
    (transcript : Valuation × Valuation → Transcript)
    (output : Transcript → Output)
    (Optimal : Valuation × Valuation → Output → Prop)
    (u v : Valuation)
    (htranscript : transcript (u, v) = transcript (v, u))
    (hnoCommon :
      ∀ out : Output, ¬ (Optimal (u, v) out ∧ Optimal (v, u) out)) :
    ¬ ∀ inst : Valuation × Valuation,
      Optimal inst (output (transcript inst)) :=
  deterministic_query_lower_bound_of_indistinguishable_pair
    transcript output Optimal htranscript hnoCommon

/--
LMMS Theorem 3.1 source-proof core: the deterministic transcript-collision
certificate rules out a universally correct minimum-envy or minimum-envy-ratio
algorithm on the supplied finite hard-instance family.
-/
theorem lmms31_query_lower_bound_from_transcript_certificate
    {Instance Transcript Output : Type*}
    [Fintype Instance] [Fintype Transcript]
    (transcript : Instance → Transcript)
    (output : Transcript → Output)
    (Optimal : Instance → Output → Prop)
    (hcard : Fintype.card Transcript < Fintype.card Instance)
    (hnoCommon :
      ∀ i j : Instance, i ≠ j → transcript i = transcript j →
        ∀ out : Output, ¬ (Optimal i out ∧ Optimal j out)) :
    ¬ ∀ i : Instance, Optimal i (output (transcript i)) :=
  deterministic_query_lower_bound_of_no_common_optimal
    transcript output Optimal hcard hnoCommon

/--
Paper-local hard-family certificate for the Theorem 3.1 minimum-envy lower
bound.  The source construction supplies a finite family of reported
two-player instances, an envy-free allocation for every instance in the
family, and the key obstruction that collided transcripts have no common
envy-free allocation.
-/
structure LMMS31HardFamilyCertificate
    (Agent Item Instance Transcript : Type*)
    [Fintype Instance] [Fintype Transcript] [DecidableEq Item] where
  goods : Finset Item
  report : Instance → FairDivisionReport Agent Item
  transcript : Instance → Transcript
  envyFree_exists :
    ∀ i, ∃ A : Allocation Agent Item,
      IsAllocationOf A goods ∧ ReportEnvyFree (report i) A
  no_common_envyFree :
    ∀ i j, i ≠ j → transcript i = transcript j →
      ∀ A : Allocation Agent Item,
        IsAllocationOf A goods →
          ¬ (ReportEnvyFree (report i) A ∧ ReportEnvyFree (report j) A)

/--
The explicit swapped pair `(u,v)` and `(v,u)` forms a hard-family certificate
once the two profiles are assigned deterministic transcripts.  This is the
source-specific bridge into the generic transcript-collision theorem.
-/
noncomputable def lmms31SwappedPairHardFamilyCertificate
    {Item Transcript : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Transcript] {k : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (u v : LMMS31HardFunction Item k)
    (hdisagree :
      ∃ S : Finset Item, S.card = k ∧ u.val S = 1 ∧ v.val S = 0)
    (transcript : LMMS31Agent → Transcript) :
    LMMS31HardFamilyCertificate
      LMMS31Agent Item LMMS31Agent Transcript where
  goods := Finset.univ
  report := lmms31SwappedCrossReport u v
  transcript := transcript
  envyFree_exists := by
    intro i
    fin_cases i
    · simpa using
        lmms31_exists_envyFree_cross_of_middle_disagreement u v hdisagree
    · simpa using
        lmms31_exists_envyFree_swap_cross_of_middle_disagreement
          hcard_items u v hdisagree
  no_common_envyFree := by
    intro i j hne _htranscript A halloc hboth
    fin_cases i <;> fin_cases j
    · exact hne rfl
    · exact
        lmms31_no_common_envyFree_cross_swap
          hcard_items u v A halloc
          ⟨by simpa using hboth.1, by simpa using hboth.2⟩
    · exact
        lmms31_no_common_envyFree_cross_swap
          hcard_items u v A halloc
          ⟨by simpa using hboth.2, by simpa using hboth.1⟩
    · exact hne rfl

/--
If the hard-family certificate is instantiated and every algorithm output that
is optimal for an instance is necessarily an envy-free allocation of the target
goods, then the transcript-count collision proves that no deterministic
algorithm can be optimal on the whole hard family.
-/
theorem lmms31_query_lower_bound_of_hard_family_certificate
    {Agent Item Instance Transcript : Type*}
    [Fintype Instance] [Fintype Transcript] [DecidableEq Item]
    (C : LMMS31HardFamilyCertificate Agent Item Instance Transcript)
    (output : Transcript → Allocation Agent Item)
    (Optimal : Instance → Allocation Agent Item → Prop)
    (hOptimal_envyFree :
      ∀ i A, Optimal i A →
        IsAllocationOf A C.goods ∧ ReportEnvyFree (C.report i) A)
    (hcard : Fintype.card Transcript < Fintype.card Instance) :
    ¬ ∀ i, Optimal i (output (C.transcript i)) := by
  refine
    deterministic_query_lower_bound_of_no_common_optimal
      C.transcript output Optimal hcard ?_
  intro i j hij htranscript A hboth
  have hi :
      IsAllocationOf A C.goods ∧ ReportEnvyFree (C.report i) A :=
    hOptimal_envyFree i A hboth.1
  have hj :
      IsAllocationOf A C.goods ∧ ReportEnvyFree (C.report j) A :=
    hOptimal_envyFree j A hboth.2
  exact C.no_common_envyFree i j hij htranscript A hi.1 ⟨hi.2, hj.2⟩

/--
Minimum-envy specialization of the hard-family certificate.  Since every
source hard instance has an envy-free allocation, a minimum-envy allocation
must itself be envy-free; the certificate obstruction then gives the Theorem
3.1 deterministic query lower-bound core for minimum envy.
-/
theorem lmms31_minimum_envy_query_lower_bound_of_hard_family_certificate
    {Agent Item Instance Transcript : Type*}
    [Fintype Agent] [Nonempty Agent]
    [Fintype Instance] [Fintype Transcript] [DecidableEq Item]
    (C : LMMS31HardFamilyCertificate Agent Item Instance Transcript)
    (output : Transcript → Allocation Agent Item)
    (hcard : Fintype.card Transcript < Fintype.card Instance) :
    ¬ ∀ i,
      MinimumReportEnvyAllocation
        (C.report i) C.goods (output (C.transcript i)) := by
  refine
    lmms31_query_lower_bound_of_hard_family_certificate
      C output
      (fun i A => MinimumReportEnvyAllocation (C.report i) C.goods A)
      ?_ hcard
  intro i A hmin
  exact
    ⟨hmin.1,
      reportEnvyFree_of_minimumReportEnvyAllocation_of_exists
        hmin (C.envyFree_exists i)⟩

/-! ## Minimum envy-ratio certificate support -/

/--
Multiplicative envy-ratio bound without division: every agent values every
other bundle by at most `rho` times her own bundle.  This is equivalent to the
paper's ratio objective when own-bundle values are positive, and is robust at
zero-valued denominators.
-/
def ReportEnvyRatioBound {Agent Item : Type*}
    (values : FairDivisionReport Agent Item)
    (A : Allocation Agent Item) (rho : ℝ) : Prop :=
  ∀ i j : Agent, values i (A j) ≤ rho * values i (A i)

/--
A target-goods allocation with minimum multiplicative envy-ratio: any
multiplicative bound achieved by another allocation of the same goods is also
achieved by this allocation.
-/
def MinimumReportEnvyRatioAllocation {Agent Item : Type*} [DecidableEq Item]
    (values : FairDivisionReport Agent Item) (goods : Finset Item)
    (A : Allocation Agent Item) : Prop :=
  IsAllocationOf A goods ∧
    ∀ B : Allocation Agent Item,
      IsAllocationOf B goods →
        ∀ rho : ℝ,
          ReportEnvyRatioBound values B rho →
            ReportEnvyRatioBound values A rho

theorem reportEnvyRatioBound_one_of_reportEnvyFree
    {Agent Item : Type*} {values : FairDivisionReport Agent Item}
    {A : Allocation Agent Item}
    (hfree : ReportEnvyFree values A) :
    ReportEnvyRatioBound values A 1 := by
  intro i j
  simpa [ReportEnvyRatioBound] using hfree i j

theorem reportEnvyFree_of_reportEnvyRatioBound_one
    {Agent Item : Type*} {values : FairDivisionReport Agent Item}
    {A : Allocation Agent Item}
    (hbound : ReportEnvyRatioBound values A 1) :
    ReportEnvyFree values A := by
  intro i j
  simpa [ReportEnvyRatioBound] using hbound i j

theorem reportEnvyFree_of_minimumReportEnvyRatioAllocation_of_exists
    {Agent Item : Type*} [DecidableEq Item]
    {values : FairDivisionReport Agent Item} {goods : Finset Item}
    {A : Allocation Agent Item}
    (hmin : MinimumReportEnvyRatioAllocation values goods A)
    (hexists : ∃ B : Allocation Agent Item,
      IsAllocationOf B goods ∧ ReportEnvyFree values B) :
    ReportEnvyFree values A := by
  obtain ⟨B, hBalloc, hBfree⟩ := hexists
  exact
    reportEnvyFree_of_reportEnvyRatioBound_one
      (hmin.2 B hBalloc 1
        (reportEnvyRatioBound_one_of_reportEnvyFree hBfree))

/--
Envy-ratio specialization of the hard-family certificate.  Since every hard
instance has an envy-free allocation, any allocation minimizing the
multiplicative envy-ratio must itself be envy-free; the same hard-family
obstruction rules out deterministic correctness on all hard instances.
-/
theorem lmms31_minimum_envy_ratio_query_lower_bound_of_hard_family_certificate
    {Agent Item Instance Transcript : Type*}
    [Fintype Instance] [Fintype Transcript] [DecidableEq Item]
    (C : LMMS31HardFamilyCertificate Agent Item Instance Transcript)
    (output : Transcript → Allocation Agent Item)
    (hcard : Fintype.card Transcript < Fintype.card Instance) :
    ¬ ∀ i,
      MinimumReportEnvyRatioAllocation
        (C.report i) C.goods (output (C.transcript i)) := by
  refine
    lmms31_query_lower_bound_of_hard_family_certificate
      C output
      (fun i A => MinimumReportEnvyRatioAllocation (C.report i) C.goods A)
      ?_ hcard
  intro i A hmin
  exact
    ⟨hmin.1,
      reportEnvyFree_of_minimumReportEnvyRatioAllocation_of_exists
        hmin (C.envyFree_exists i)⟩

/--
Concrete swapped-pair minimum-envy-ratio obstruction for Theorem 3.1.  The
same source pair used for minimum envy also rules out deterministic
minimum-ratio correctness, because each crossed instance admits an envy-free
allocation and hence any minimum-ratio allocation must be envy-free.
-/
theorem lmms31_minimum_envy_ratio_query_lower_bound_of_swapped_cross_pair
    {Item Transcript : Type*} [Fintype Item] [DecidableEq Item] {k : ℕ}
    (hcard_items : Fintype.card Item = 2 * k)
    (u v : LMMS31HardFunction Item k)
    (hdisagree :
      ∃ S : Finset Item, S.card = k ∧ u.val S = 1 ∧ v.val S = 0)
    (transcript : LMMS31Agent → Transcript)
    (output : Transcript → Allocation LMMS31Agent Item)
    (htranscript :
      transcript (0 : LMMS31Agent) = transcript (1 : LMMS31Agent)) :
    ¬ ∀ inst : LMMS31Agent,
      MinimumReportEnvyRatioAllocation
        (lmms31SwappedCrossReport u v inst)
        (Finset.univ : Finset Item)
        (output (transcript inst)) := by
  classical
  intro hcorrect
  let A : Allocation LMMS31Agent Item := output (transcript (0 : LMMS31Agent))
  have hleft :
      MinimumReportEnvyRatioAllocation
        (lmms31CrossReport u v)
        (Finset.univ : Finset Item) A := by
    simpa [A] using hcorrect (0 : LMMS31Agent)
  have hright :
      MinimumReportEnvyRatioAllocation
        (lmms31CrossReport v u)
        (Finset.univ : Finset Item) A := by
    simpa [A, htranscript] using hcorrect (1 : LMMS31Agent)
  have hfree_left :
      ReportEnvyFree (lmms31CrossReport u v) A := by
    have hexists :=
      lmms31_exists_envyFree_cross_of_middle_disagreement u v hdisagree
    exact
      reportEnvyFree_of_minimumReportEnvyRatioAllocation_of_exists
        hleft hexists
  have hfree_right :
      ReportEnvyFree (lmms31CrossReport v u) A := by
    have hexists :=
      lmms31_exists_envyFree_swap_cross_of_middle_disagreement
        hcard_items u v hdisagree
    exact
      reportEnvyFree_of_minimumReportEnvyRatioAllocation_of_exists
        hright hexists
  exact
    lmms31_no_common_envyFree_cross_swap
      hcard_items u v A hleft.1 ⟨hfree_left, hfree_right⟩

/--
LMMS Theorem 3.1 swapped-instance certificate: once the source hard-family
counting step has produced two utility functions `u` and `v` whose swapped
two-player instances have the same deterministic transcript, and the source
optimality argument proves that no allocation is optimal for both, no
deterministic transcript-based algorithm can be correct on every hard instance.
-/
theorem lmms31_query_lower_bound_from_swapped_pair_certificate
    {Valuation Transcript Output : Type*}
    (transcript : Valuation × Valuation → Transcript)
    (output : Transcript → Output)
    (Optimal : Valuation × Valuation → Output → Prop)
    (u v : Valuation)
    (htranscript : transcript (u, v) = transcript (v, u))
    (hnoCommon :
      ∀ out : Output, ¬ (Optimal (u, v) out ∧ Optimal (v, u) out)) :
    ¬ ∀ inst : Valuation × Valuation,
      Optimal inst (output (transcript inst)) :=
  deterministic_query_lower_bound_of_swapped_indistinguishable_pair
    transcript output Optimal u v htranscript hnoCommon

end Theorem31
end LMMS04FairDivision
