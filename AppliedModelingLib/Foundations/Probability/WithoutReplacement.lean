import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.Foundations.Probability.Conditional
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Finite Without-Replacement Sampling

Reusable finite PMFs for sequential weighted draws without replacement.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- Insert on the left and erase from the right preserves a union when the
inserted element belongs to the right set. -/
theorem finset_insert_union_erase_eq_union_of_mem {α : Type*} [DecidableEq α]
    {a : α} {s t : Finset α} (ha : a ∈ t) :
    insert a s ∪ t.erase a = s ∪ t := by
  classical
  ext x
  by_cases hxa : x = a
  · subst x
    simp [ha]
  · simp [hxa]

/-- Prepend one element to a `Fin k`-indexed list. -/
def finCons {α : Type*} {k : ℕ} (head : α) (tail : Fin k → α) :
    Fin (k + 1) → α
  | ⟨0, _h⟩ => head
  | ⟨n + 1, h⟩ => tail ⟨n, Nat.succ_lt_succ_iff.mp h⟩

@[simp]
theorem finCons_zero {α : Type*} {k : ℕ} (head : α) (tail : Fin k → α) :
    finCons head tail ⟨0, Nat.succ_pos k⟩ = head := rfl

@[simp]
theorem finCons_succ {α : Type*} {k : ℕ}
    (head : α) (tail : Fin k → α) (i : Fin k) :
    finCons head tail i.succ = tail i := by
  cases i
  rfl

theorem finCons_injective {α : Type*} {k : ℕ}
    {head : α} {tail : Fin k → α}
    (hhead_not_tail : ∀ i : Fin k, tail i ≠ head)
    (htail : Function.Injective tail) :
    Function.Injective (finCons head tail) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          exfalso
          have hhead_eq : head = tail j := by
            simpa using hij
          exact hhead_not_tail j hhead_eq.symm
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          exfalso
          have htail_eq : tail i = head := by
            simpa using hij
          exact hhead_not_tail i htail_eq
      | succ j =>
          exact congrArg Fin.succ (htail (by simpa using hij))

/-- Drop the first entry of a `Fin (k + 1)`-indexed list. -/
def finTail {α : Type*} {k : ℕ} (list : Fin (k + 1) → α) :
    Fin k → α :=
  fun i => list i.succ

@[simp]
theorem finTail_finCons {α : Type*} {k : ℕ}
    (head : α) (tail : Fin k → α) :
    finTail (finCons head tail) = tail := by
  funext i
  simp [finTail]

theorem finCons_head_tail {α : Type*} {k : ℕ}
    (list : Fin (k + 1) → α) :
    finCons (list ⟨0, Nat.succ_pos k⟩) (finTail list) = list := by
  funext i
  cases i using Fin.cases with
  | zero =>
      rfl
  | succ i =>
      simp [finTail]

/--
Length-`k` lists that are injective and avoid an initial forbidden set.
-/
abbrev finiteFreshList (α : Type*) (k : ℕ) (forbidden : Finset α) :=
  {list : Fin k → α // Function.Injective list ∧ ∀ slot, list slot ∉ forbidden}

/-- The unique fresh list of length zero. -/
def finiteFreshListNil (α : Type*) (forbidden : Finset α) :
    finiteFreshList α 0 forbidden :=
  ⟨fun i => Fin.elim0 i,
    by
      intro i _j _h
      exact Fin.elim0 i,
    by
      intro i
      exact Fin.elim0 i⟩

/-- Cons an available head onto a tail that avoids the enlarged forbidden set. -/
def finiteFreshListCons {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden)) :
    finiteFreshList α (k + 1) forbidden :=
  ⟨finCons head.1 tail.1,
    by
      refine finCons_injective ?_ tail.2.1
      intro i htail_eq_head
      exact tail.2.2 i (by
        rw [htail_eq_head]
        simp)
    ,
    by
      intro slot
      cases slot using Fin.cases with
      | zero =>
          exact head.2
      | succ i =>
          intro hforbidden
          exact tail.2.2 i
            (Finset.mem_insert.mpr (Or.inr hforbidden))⟩

@[simp]
theorem finiteFreshListCons_zero {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden)) :
    (finiteFreshListCons head tail).1 ⟨0, Nat.succ_pos k⟩ = head.1 := rfl

@[simp]
theorem finiteFreshListCons_succ {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden))
    (i : Fin k) :
    (finiteFreshListCons head tail).1 i.succ = tail.1 i := by
  cases i
  rfl

/--
The tail of a fresh list whose head is a specified available point.  The tail
avoids both the old forbidden set and that realized head.
-/
def finiteFreshListTailOfHead {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (sample : finiteFreshList α (k + 1) forbidden)
    (head : {a // a ∉ forbidden})
    (hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head.1) :
    finiteFreshList α k (insert head.1 forbidden) :=
  ⟨finTail sample.1,
    by
      intro i j hij
      apply Fin.ext
      have hsucc :
          i.succ = j.succ :=
        sample.2.1 (by simpa [finTail] using hij)
      have hval := congrArg Fin.val hsucc
      simp at hval
      omega,
    by
      intro i hmem
      rw [Finset.mem_insert] at hmem
      cases hmem with
      | inl htail_head =>
          have htail_eq_head : sample.1 i.succ = head.1 := by
            simpa [finTail] using htail_head
          have hslot_eq_zero :
              i.succ = (⟨0, Nat.succ_pos k⟩ : Fin (k + 1)) := by
            exact sample.2.1 (htail_eq_head.trans hhead.symm)
          exact Fin.succ_ne_zero i hslot_eq_zero
      | inr hforbidden =>
          exact sample.2.2 i.succ hforbidden⟩

@[simp]
theorem finiteFreshListTailOfHead_cons {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden))
    (hhead : (finiteFreshListCons head tail).1 ⟨0, Nat.succ_pos k⟩ = head.1) :
    finiteFreshListTailOfHead (finiteFreshListCons head tail) head hhead = tail := by
  ext i
  simp [finiteFreshListTailOfHead, finTail]

theorem finiteFreshListCons_tailOfHead {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (sample : finiteFreshList α (k + 1) forbidden)
    (head : {a // a ∉ forbidden})
    (hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head.1) :
    finiteFreshListCons head (finiteFreshListTailOfHead sample head hhead) =
      sample := by
  ext i
  cases i using Fin.cases with
  | zero =>
      simpa using hhead.symm
  | succ i =>
      simp [finiteFreshListTailOfHead, finTail]

@[simp]
theorem finiteFreshListTailOfHead_proof_irrel {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (sample : finiteFreshList α (k + 1) forbidden)
    (head : {a // a ∉ forbidden})
    (h₁ h₂ : sample.1 ⟨0, Nat.succ_pos k⟩ = head.1) :
    finiteFreshListTailOfHead sample head h₁ =
      finiteFreshListTailOfHead sample head h₂ := by
  ext i
  rfl

/-- The set of entries appearing in the first `r` slots of a fresh list. -/
noncomputable def finiteFreshListPrefixSet {α : Type*} [DecidableEq α]
    {k : ℕ} {forbidden : Finset α}
    (r : ℕ) (sample : finiteFreshList α k forbidden) : Finset α :=
  ((Finset.univ : Finset (Fin k)).filter fun slot => slot.val < r).image sample.1

theorem finiteFreshList_mem_prefixSet_iff {α : Type*} [DecidableEq α]
    {k r : ℕ} {forbidden : Finset α}
    (sample : finiteFreshList α k forbidden) (a : α) :
    a ∈ finiteFreshListPrefixSet r sample ↔
      ∃ slot : Fin k, slot.val < r ∧ sample.1 slot = a := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨slot, hslot, rfl⟩
    exact ⟨slot, (Finset.mem_filter.mp hslot).2, rfl⟩
  · rintro ⟨slot, hslot_lt, rfl⟩
    exact Finset.mem_image.mpr
      ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hslot_lt⟩, rfl⟩

@[simp]
theorem finiteFreshListPrefixSet_zero {α : Type*} [DecidableEq α]
    {k : ℕ} {forbidden : Finset α}
    (sample : finiteFreshList α k forbidden) :
    finiteFreshListPrefixSet 0 sample = ∅ := by
  classical
  ext a
  simp [finiteFreshList_mem_prefixSet_iff]

@[simp]
theorem finiteFreshListPrefixSet_cons_succ {α : Type*} [DecidableEq α]
    {k r : ℕ} {forbidden : Finset α}
    (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden)) :
    finiteFreshListPrefixSet (r + 1) (finiteFreshListCons head tail) =
      insert head.1 (finiteFreshListPrefixSet r tail) := by
  classical
  ext a
  constructor
  · intro ha
    rcases (finiteFreshList_mem_prefixSet_iff
      (finiteFreshListCons head tail) a).1 ha with
      ⟨slot, hslot_lt, hslot_eq⟩
    cases slot using Fin.cases with
    | zero =>
        have ha_head : a = head.1 := by
          simpa using hslot_eq.symm
        exact Finset.mem_insert.mpr (Or.inl ha_head)
    | succ i =>
        have hi_lt : i.val < r := by
          simpa using hslot_lt
        exact Finset.mem_insert.mpr
          (Or.inr ((finiteFreshList_mem_prefixSet_iff tail a).2
            ⟨i, hi_lt, by simpa using hslot_eq⟩))
  · intro ha
    rcases Finset.mem_insert.mp ha with hhead | htail
    · exact (finiteFreshList_mem_prefixSet_iff
        (finiteFreshListCons head tail) a).2
        ⟨⟨0, Nat.succ_pos k⟩, Nat.succ_pos r, by
          rw [hhead]
          rfl⟩
    · rcases (finiteFreshList_mem_prefixSet_iff tail a).1 htail with
        ⟨slot, hslot_lt, hslot_eq⟩
      exact (finiteFreshList_mem_prefixSet_iff
        (finiteFreshListCons head tail) a).2
        ⟨slot.succ, by simpa using hslot_lt, by simpa using hslot_eq⟩

theorem finiteFreshList_head_not_mem_tail_prefixSet {α : Type*} [DecidableEq α]
    {k r : ℕ} {forbidden : Finset α}
    (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden)) :
    head.1 ∉ finiteFreshListPrefixSet r tail := by
  intro hmem
  rcases (finiteFreshList_mem_prefixSet_iff tail head.1).1 hmem with
    ⟨slot, _hslot_lt, hslot_eq⟩
  exact tail.2.2 slot (by
    rw [hslot_eq]
    simp)

theorem finiteFreshListPrefixSet_cons_succ_eq_iff {α : Type*} [DecidableEq α]
    {k r : ℕ} {forbidden : Finset α}
    (head : {a // a ∉ forbidden})
    (tail : finiteFreshList α k (insert head.1 forbidden))
    (previous : Finset α) :
    finiteFreshListPrefixSet (r + 1) (finiteFreshListCons head tail) =
        previous ↔
      finiteFreshListPrefixSet r tail = previous.erase head.1 ∧
        head.1 ∈ previous := by
  classical
  have hnot : head.1 ∉ finiteFreshListPrefixSet r tail :=
    finiteFreshList_head_not_mem_tail_prefixSet head tail
  rw [finiteFreshListPrefixSet_cons_succ]
  constructor
  · intro hprev
    have hhead_mem : head.1 ∈ previous := by
      rw [← hprev]
      simp
    constructor
    · rw [← hprev]
      simp [hnot]
    · exact hhead_mem
  · rintro ⟨htail, hhead_mem⟩
    rw [htail]
    exact Finset.insert_erase hhead_mem

theorem finiteFreshListPrefixSet_one {α : Type*} [DecidableEq α]
    {k : ℕ} {forbidden : Finset α}
    (sample : finiteFreshList α (k + 1) forbidden) :
    finiteFreshListPrefixSet 1 sample =
      {sample.1 ⟨0, Nat.succ_pos k⟩} := by
  classical
  ext a
  constructor
  · intro ha
    rcases (finiteFreshList_mem_prefixSet_iff sample a).1 ha with
      ⟨slot, hslot_lt, hslot_eq⟩
    have hslot_zero : slot = ⟨0, Nat.succ_pos k⟩ := by
      apply Fin.ext
      change slot.val = 0
      omega
    rw [hslot_zero] at hslot_eq
    exact Finset.mem_singleton.mpr hslot_eq.symm
  · intro ha
    rw [Finset.mem_singleton] at ha
    exact (finiteFreshList_mem_prefixSet_iff sample a).2
      ⟨⟨0, Nat.succ_pos k⟩, by norm_num, by simpa [ha]⟩

/--
The first `r` entries of `sample` agree, in order, with a realized fresh
prefix.  The explicit `r ≤ k` argument lets this predicate compare prefixes of
different ambient lengths without changing the underlying ordered values.
-/
def finiteFreshListHasPrefix {α : Type*}
    {r k : ℕ} {forbidden : Finset α} (hrk : r ≤ k)
    (pref : finiteFreshList α r forbidden)
    (sample : finiteFreshList α k forbidden) : Prop :=
  ∀ slot ∈ (Finset.univ : Finset (Fin r)),
    sample.1 ⟨slot.val, lt_of_lt_of_le slot.2 hrk⟩ = pref.1 slot

instance finiteFreshListHasPrefix_decidable
    {α : Type*} [DecidableEq α]
    {r k : ℕ} {forbidden : Finset α} (hrk : r ≤ k)
    (pref : finiteFreshList α r forbidden)
    (sample : finiteFreshList α k forbidden) :
    Decidable (finiteFreshListHasPrefix hrk pref sample) := by
  classical
  unfold finiteFreshListHasPrefix
  infer_instance

/-- The ordered first `r` entries of a fresh list, as a fresh list. -/
def finiteFreshListPrefix {α : Type*}
    {r k : ℕ} {forbidden : Finset α} (hrk : r ≤ k)
    (sample : finiteFreshList α k forbidden) :
    finiteFreshList α r forbidden :=
  ⟨fun slot => sample.1 ⟨slot.val, lt_of_lt_of_le slot.2 hrk⟩,
    by
      intro i j hij
      apply Fin.ext
      have hfull :
          (⟨i.val, lt_of_lt_of_le i.2 hrk⟩ : Fin k) =
            ⟨j.val, lt_of_lt_of_le j.2 hrk⟩ :=
        sample.2.1 hij
      exact congrArg (fun slot : Fin k => slot.val) hfull,
    by
      intro slot
      exact sample.2.2 ⟨slot.val, lt_of_lt_of_le slot.2 hrk⟩⟩

@[simp]
theorem finiteFreshListPrefix_apply {α : Type*}
    {r k : ℕ} {forbidden : Finset α} (hrk : r ≤ k)
    (sample : finiteFreshList α k forbidden) (slot : Fin r) :
    (finiteFreshListPrefix hrk sample).1 slot =
      sample.1 ⟨slot.val, lt_of_lt_of_le slot.2 hrk⟩ := rfl

/-- A fresh list has its own extracted prefix. -/
theorem finiteFreshListHasPrefix_prefix
    {α : Type*} {r k : ℕ} {forbidden : Finset α} (hrk : r ≤ k)
    (sample : finiteFreshList α k forbidden) :
    finiteFreshListHasPrefix hrk (finiteFreshListPrefix hrk sample)
      sample := by
  intro slot _hslot
  rfl

/-- Prefix agreement is equivalently equality with the extracted prefix. -/
theorem finiteFreshListHasPrefix_iff_prefix_eq
    {α : Type*} {r k : ℕ} {forbidden : Finset α} (hrk : r ≤ k)
    (pref : finiteFreshList α r forbidden)
    (sample : finiteFreshList α k forbidden) :
    finiteFreshListHasPrefix hrk pref sample ↔
      finiteFreshListPrefix hrk sample = pref := by
  constructor
  · intro hprefix
    ext slot
    exact hprefix slot (Finset.mem_univ slot)
  · intro hprefix
    rw [← hprefix]
    exact finiteFreshListHasPrefix_prefix hrk sample

/--
Conditioning a fresh list on a fixed realized head leaves exactly the fresh-tail
sample space with the head added to the forbidden set.
-/
def finiteFreshListHeadEquivTail {α : Type*} [DecidableEq α] {k : ℕ}
    {forbidden : Finset α}
    (head : {a // a ∉ forbidden}) :
    {sample : finiteFreshList α (k + 1) forbidden //
      sample.1 ⟨0, Nat.succ_pos k⟩ = head.1} ≃
      finiteFreshList α k (insert head.1 forbidden) where
  toFun sample := finiteFreshListTailOfHead sample.1 head sample.2
  invFun tail := ⟨finiteFreshListCons head tail, rfl⟩
  left_inv := by
    intro sample
    apply Subtype.ext
    exact finiteFreshListCons_tailOfHead sample.1 head sample.2
  right_inv := by
    intro tail
    simp

/--
Relabel fresh lists by an equivalence that transports the forbidden set.
This is the basic exchangeability map for ordered samples without replacement.
-/
def finiteFreshListRelabelEquiv {α β : Type*}
    [DecidableEq α] [DecidableEq β] {k : ℕ}
    {forbidden : Finset α} {targetForbidden : Finset β}
    (e : α ≃ β)
    (hmem : ∀ a, e a ∈ targetForbidden ↔ a ∈ forbidden) :
    finiteFreshList α k forbidden ≃ finiteFreshList β k targetForbidden where
  toFun sample :=
    ⟨fun slot => e (sample.1 slot), by
      intro i j hij
      exact sample.2.1 (e.injective hij), by
      intro slot hforbidden
      exact sample.2.2 slot ((hmem (sample.1 slot)).1 hforbidden)⟩
  invFun sample :=
    ⟨fun slot => e.symm (sample.1 slot), by
      intro i j hij
      exact sample.2.1 (e.symm.injective hij), by
      intro slot hforbidden
      have htarget :
          e (e.symm (sample.1 slot)) ∈ targetForbidden :=
        (hmem (e.symm (sample.1 slot))).2 hforbidden
      exact sample.2.2 slot (by simpa using htarget)⟩
  left_inv := by
    intro sample
    ext slot
    simp
  right_inv := by
    intro sample
    ext slot
    simp

/--
Sequential weighted sampling without replacement, starting from an initial
forbidden set.  The budget proof says there are enough alternatives to draw
`k` fresh elements.  Positivity of every non-full available set is supplied as
a reusable assumption, typically from full support of the base weights.
-/
noncomputable def finiteWithoutReplacementPMF
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden) :
    (k : ℕ) → (forbidden : Finset α) →
      forbidden.card + k ≤ Fintype.card α →
        PMF (finiteFreshList α k forbidden)
  | 0, forbidden, _hbudget => PMF.pure (finiteFreshListNil α forbidden)
  | k + 1, forbidden, hbudget =>
      (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega))).bind fun head =>
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k (insert head.1 forbidden)
          (by
            rw [Finset.card_insert_of_notMem head.2]
            omega)).map (finiteFreshListCons head)
termination_by k forbidden hbudget => k

/--
The first draw of the recursive without-replacement sampler has exactly the
available weighted law from the current forbidden set.
-/
theorem finiteWithoutReplacementPMF_head_prob
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (head₀ : {a // a ∉ forbidden}) :
    pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample =>
          sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1) =
      (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega)) head₀).toReal := by
  classical
  rw [finiteWithoutReplacementPMF]
  rw [pmfProb_bind]
  let headLaw :=
    finiteWeightedPMFAvailable
      baseWeight forbidden hbase_nonneg
      (havailable forbidden (by omega))
  have hinner : ∀ head : {a // a ∉ forbidden},
      pmfProb
          ((finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega)).map (finiteFreshListCons head))
          (fun sample =>
            sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1) =
        if head = head₀ then (1 : ℝ) else 0 := by
    intro head
    rw [pmfProb_map]
    by_cases hhead : head = head₀
    · subst head
      simpa using
        (pmfProb_eq_one_of_forall _ _ (by
          intro tail
          rfl))
    · have hval_ne : head.1 ≠ head₀.1 := by
        intro hval
        exact hhead (Subtype.ext hval)
      simpa [hhead] using
        (pmfProb_eq_zero_of_no_mass _ _ (by
        intro tail htail
        exact False.elim (hval_ne (by simpa using htail)))
        )
  calc
    pmfExp headLaw
        (fun head =>
          pmfProb
            ((finiteWithoutReplacementPMF
              baseWeight hbase_nonneg havailable
              k (insert head.1 forbidden)
              (by
                rw [Finset.card_insert_of_notMem head.2]
                omega)).map (finiteFreshListCons head))
            (fun sample =>
              sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1))
        = pmfExp headLaw (fun head => if head = head₀ then (1 : ℝ) else 0) := by
            refine pmfExp_congr headLaw ?_
            intro head
            exact hinner head
    _ = pmfProb headLaw (fun head => head = head₀) := rfl
    _ = (headLaw head₀).toReal := pmfProb_singleton headLaw head₀
    _ = (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega)) head₀).toReal := rfl

/--
Joint law of the first draw and a tail event for the recursive
without-replacement sampler.
-/
theorem finiteWithoutReplacementPMF_head_tail_prob
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (head₀ : {a // a ∉ forbidden})
    (q : finiteFreshList α k (insert head₀.1 forbidden) → Prop)
    [DecidablePred q]
    [DecidablePred fun sample : finiteFreshList α (k + 1) forbidden =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
        q (finiteFreshListTailOfHead sample head₀ hhead)] :
    pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample =>
          ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
            q (finiteFreshListTailOfHead sample head₀ hhead)) =
      (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega)) head₀).toReal *
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head₀.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head₀.2]
              omega))
          q := by
  classical
  rw [finiteWithoutReplacementPMF]
  rw [pmfProb_bind]
  let headLaw :=
    finiteWeightedPMFAvailable
      baseWeight forbidden hbase_nonneg
      (havailable forbidden (by omega))
  let target : finiteFreshList α (k + 1) forbidden → Prop :=
    fun sample =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
        q (finiteFreshListTailOfHead sample head₀ hhead)
  let tailLaw :
      (head : {a // a ∉ forbidden}) →
        PMF (finiteFreshList α k (insert head.1 forbidden)) :=
    fun head =>
      finiteWithoutReplacementPMF
        baseWeight hbase_nonneg havailable
        k (insert head.1 forbidden)
        (by
          rw [Finset.card_insert_of_notMem head.2]
          omega)
  have hinner : ∀ head : {a // a ∉ forbidden},
      pmfProb
          ((tailLaw head).map (finiteFreshListCons head))
          target =
        if head = head₀ then pmfProb (tailLaw head₀) q else 0 := by
    intro head
    by_cases hhead_eq : head = head₀
    · subst head
      rw [pmfProb_map]
      simpa using
        (pmfProb_congr (tailLaw head₀)
          (p := fun tail => target (finiteFreshListCons head₀ tail))
          (q := q)
          (by
            intro tail
            constructor
            · rintro ⟨hrealized, hq⟩
              simpa [target] using hq
            · intro hq
              refine ⟨rfl, ?_⟩
              simpa [target] using hq))
    · have hval_ne : head.1 ≠ head₀.1 := by
        intro hval
        exact hhead_eq (Subtype.ext hval)
      rw [pmfProb_map]
      simpa [hhead_eq] using
        (pmfProb_eq_zero_of_no_mass (tailLaw head)
          (fun tail => target (finiteFreshListCons head tail))
          (by
            intro tail htarget
            rcases htarget with ⟨hrealized, _hq⟩
            exact False.elim (hval_ne (by simpa [target] using hrealized))))
  calc
    pmfExp headLaw
        (fun head =>
          pmfProb
            ((tailLaw head).map (finiteFreshListCons head))
            target)
        = pmfExp headLaw
            (fun head =>
              if head = head₀ then pmfProb (tailLaw head₀) q else 0) := by
            refine pmfExp_congr headLaw ?_
            intro head
            exact hinner head
    _ = pmfExp headLaw
          (fun head =>
            (if head = head₀ then (1 : ℝ) else 0) *
              pmfProb (tailLaw head₀) q) := by
            refine pmfExp_congr headLaw ?_
            intro head
            by_cases hhead : head = head₀ <;> simp [hhead]
    _ = pmfProb headLaw (fun head => head = head₀) *
          pmfProb (tailLaw head₀) q := by
            rw [pmfExp_mul_const]
            rfl
    _ = (headLaw head₀).toReal * pmfProb (tailLaw head₀) q := by
            rw [pmfProb_singleton]
    _ = (finiteWeightedPMFAvailable
          baseWeight forbidden hbase_nonneg
          (havailable forbidden (by omega)) head₀).toReal *
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head₀.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head₀.2]
              omega))
          q := rfl

/--
First-step recurrence for any event under the recursive without-replacement
sampler: sum over the realized head and then evaluate the event on the
corresponding consed tail.
-/
theorem finiteWithoutReplacementPMF_event_prob_succ_eq_sum_head
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (event : finiteFreshList α (k + 1) forbidden → Prop)
    [DecidablePred event] :
    pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        event =
      ∑ head : {a // a ∉ forbidden},
        (finiteWeightedPMFAvailable
          baseWeight forbidden hbase_nonneg
          (havailable forbidden (by omega)) head).toReal *
          pmfProb
            (finiteWithoutReplacementPMF
              baseWeight hbase_nonneg havailable
              k (insert head.1 forbidden)
              (by
                rw [Finset.card_insert_of_notMem head.2]
                omega))
            (fun tail => event (finiteFreshListCons head tail)) := by
  classical
  rw [finiteWithoutReplacementPMF]
  rw [pmfProb_bind]
  let headLaw :=
    finiteWeightedPMFAvailable
      baseWeight forbidden hbase_nonneg
      (havailable forbidden (by omega))
  let tailLaw :
      (head : {a // a ∉ forbidden}) →
        PMF (finiteFreshList α k (insert head.1 forbidden)) :=
    fun head =>
      finiteWithoutReplacementPMF
        baseWeight hbase_nonneg havailable
        k (insert head.1 forbidden)
        (by
          rw [Finset.card_insert_of_notMem head.2]
          omega)
  calc
    pmfExp headLaw
        (fun head =>
          pmfProb ((tailLaw head).map (finiteFreshListCons head)) event)
        =
      pmfExp headLaw
        (fun head =>
          pmfProb (tailLaw head)
            (fun tail => event (finiteFreshListCons head tail))) := by
        refine pmfExp_congr headLaw ?_
        intro head
        rw [pmfProb_map]
    _ =
      ∑ head : {a // a ∉ forbidden},
        (finiteWeightedPMFAvailable
          baseWeight forbidden hbase_nonneg
          (havailable forbidden (by omega)) head).toReal *
          pmfProb
            (finiteWithoutReplacementPMF
              baseWeight hbase_nonneg havailable
              k (insert head.1 forbidden)
              (by
                rw [Finset.card_insert_of_notMem head.2]
                omega))
            (fun tail => event (finiteFreshListCons head tail)) := by
        rfl

/--
First-step recurrence for the event that a fixed atom is omitted by the whole
without-replacement list.
-/
theorem finiteWithoutReplacementPMF_omit_atom_succ_prob_eq_sum_head
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (target : α) :
    pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample => ∀ slot : Fin (k + 1), sample.1 slot ≠ target) =
      ∑ head : {a // a ∉ forbidden},
        if head.1 = target then 0 else
          (finiteWeightedPMFAvailable
            baseWeight forbidden hbase_nonneg
            (havailable forbidden (by omega)) head).toReal *
            pmfProb
              (finiteWithoutReplacementPMF
                baseWeight hbase_nonneg havailable
                k (insert head.1 forbidden)
                (by
                  rw [Finset.card_insert_of_notMem head.2]
                  omega))
              (fun tail => ∀ slot : Fin k, tail.1 slot ≠ target) := by
  classical
  rw [finiteWithoutReplacementPMF_event_prob_succ_eq_sum_head
    baseWeight hbase_nonneg havailable forbidden hbudget
    (fun sample : finiteFreshList α (k + 1) forbidden =>
      ∀ slot : Fin (k + 1), sample.1 slot ≠ target)]
  refine Finset.sum_congr rfl ?_
  intro head _hhead
  by_cases hhead_target : head.1 = target
  · have hzero :
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega))
          (fun tail =>
            ∀ slot : Fin (k + 1),
              (finiteFreshListCons head tail).1 slot ≠ target) = 0 := by
      refine pmfProb_eq_zero_of_no_mass _ _ ?_
      intro tail htail
      exact False.elim
        (htail ⟨0, Nat.succ_pos k⟩ (by
          simpa using hhead_target))
    simp [hhead_target, hzero]
  · have htail_congr :
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega))
          (fun tail =>
            ∀ slot : Fin (k + 1),
              (finiteFreshListCons head tail).1 slot ≠ target) =
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega))
          (fun tail => ∀ slot : Fin k, tail.1 slot ≠ target) := by
      refine pmfProb_congr _ ?_
      intro tail
      constructor
      · intro htail slot hslot
        exact htail slot.succ (by simpa using hslot)
      · intro htail slot
        cases slot using Fin.cases with
        | zero =>
            simpa using hhead_target
        | succ slot =>
            exact htail slot
    simp [hhead_target, htail_congr]

/--
First-step recurrence for the event that two fixed atoms are both omitted by
the whole without-replacement list.
-/
theorem finiteWithoutReplacementPMF_omit_pair_succ_prob_eq_sum_head
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (i j : α) :
    pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample =>
          (∀ slot : Fin (k + 1), sample.1 slot ≠ i) ∧
            (∀ slot : Fin (k + 1), sample.1 slot ≠ j)) =
      ∑ head : {a // a ∉ forbidden},
        if head.1 = i ∨ head.1 = j then 0 else
          (finiteWeightedPMFAvailable
            baseWeight forbidden hbase_nonneg
            (havailable forbidden (by omega)) head).toReal *
            pmfProb
              (finiteWithoutReplacementPMF
                baseWeight hbase_nonneg havailable
                k (insert head.1 forbidden)
                (by
                  rw [Finset.card_insert_of_notMem head.2]
                  omega))
              (fun tail =>
                (∀ slot : Fin k, tail.1 slot ≠ i) ∧
                  (∀ slot : Fin k, tail.1 slot ≠ j)) := by
  classical
  rw [finiteWithoutReplacementPMF_event_prob_succ_eq_sum_head
    baseWeight hbase_nonneg havailable forbidden hbudget
    (fun sample : finiteFreshList α (k + 1) forbidden =>
      (∀ slot : Fin (k + 1), sample.1 slot ≠ i) ∧
        (∀ slot : Fin (k + 1), sample.1 slot ≠ j))]
  refine Finset.sum_congr rfl ?_
  intro head _hhead
  by_cases hhead_bad : head.1 = i ∨ head.1 = j
  · have hzero :
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega))
          (fun tail =>
            (∀ slot : Fin (k + 1),
              (finiteFreshListCons head tail).1 slot ≠ i) ∧
              (∀ slot : Fin (k + 1),
                (finiteFreshListCons head tail).1 slot ≠ j)) = 0 := by
      refine pmfProb_eq_zero_of_no_mass _ _ ?_
      intro tail htail
      rcases hhead_bad with hi | hj
      · exact False.elim
          (htail.1 ⟨0, Nat.succ_pos k⟩ (by simpa using hi))
      · exact False.elim
          (htail.2 ⟨0, Nat.succ_pos k⟩ (by simpa using hj))
    simp [hhead_bad, hzero]
  · have hhead_i : head.1 ≠ i := by
      intro hi
      exact hhead_bad (Or.inl hi)
    have hhead_j : head.1 ≠ j := by
      intro hj
      exact hhead_bad (Or.inr hj)
    have htail_congr :
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega))
          (fun tail =>
            (∀ slot : Fin (k + 1),
              (finiteFreshListCons head tail).1 slot ≠ i) ∧
              (∀ slot : Fin (k + 1),
                (finiteFreshListCons head tail).1 slot ≠ j)) =
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega))
          (fun tail =>
            (∀ slot : Fin k, tail.1 slot ≠ i) ∧
              (∀ slot : Fin k, tail.1 slot ≠ j)) := by
      refine pmfProb_congr _ ?_
      intro tail
      constructor
      · intro htail
        constructor
        · intro slot hslot
          exact htail.1 slot.succ (by simpa using hslot)
        · intro slot hslot
          exact htail.2 slot.succ (by simpa using hslot)
      · intro htail
        constructor
        · intro slot
          cases slot using Fin.cases with
          | zero =>
              simpa using hhead_i
          | succ slot =>
              exact htail.1 slot
        · intro slot
          cases slot using Fin.cases with
          | zero =>
              simpa using hhead_j
          | succ slot =>
              exact htail.2 slot
    simp [hhead_bad, htail_congr]

/--
Conditional tail law for the recursive without-replacement sampler after a
positive-probability realized head.
-/
theorem finiteWithoutReplacementPMF_conditional_tail_prob
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (head₀ : {a // a ∉ forbidden})
    (hhead_pos :
      0 < (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega)) head₀).toReal)
    (q : finiteFreshList α k (insert head₀.1 forbidden) → Prop)
    [DecidablePred q]
    [DecidablePred fun sample : finiteFreshList α (k + 1) forbidden =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
        q (finiteFreshListTailOfHead sample head₀ hhead)] :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample => sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1)
        (fun sample =>
          ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
            q (finiteFreshListTailOfHead sample head₀ hhead)) =
      pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k (insert head₀.1 forbidden)
          (by
            rw [Finset.card_insert_of_notMem head₀.2]
            omega))
        q := by
  classical
  let μ :=
    finiteWithoutReplacementPMF
      baseWeight hbase_nonneg havailable
      (k + 1) forbidden hbudget
  let p : finiteFreshList α (k + 1) forbidden → Prop :=
    fun sample => sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1
  let target : finiteFreshList α (k + 1) forbidden → Prop :=
    fun sample =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
        q (finiteFreshListTailOfHead sample head₀ hhead)
  have hp_prob :
      pmfProb μ p =
        (finiteWeightedPMFAvailable
          baseWeight forbidden hbase_nonneg
          (havailable forbidden (by omega)) head₀).toReal := by
    simpa [μ, p] using
      (finiteWithoutReplacementPMF_head_prob
        baseWeight hbase_nonneg havailable
        forbidden hbudget head₀)
  have hp_pos : 0 < pmfProb μ p := by
    rw [hp_prob]
    exact hhead_pos
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p target hp_pos]
  have hinter :
      pmfProb μ (fun sample => p sample ∧ target sample) =
        pmfProb μ target := by
    exact pmfProb_inter_eq_right_of_imp μ p target (by
      intro sample htarget
      rcases htarget with ⟨hrealized, _hq⟩
      exact hrealized)
  rw [hinter]
  have hjoint :
      pmfProb μ target =
        (finiteWeightedPMFAvailable
          baseWeight forbidden hbase_nonneg
          (havailable forbidden (by omega)) head₀).toReal *
          pmfProb
            (finiteWithoutReplacementPMF
              baseWeight hbase_nonneg havailable
              k (insert head₀.1 forbidden)
              (by
                rw [Finset.card_insert_of_notMem head₀.2]
                omega))
            q := by
    simpa [μ, target] using
      (finiteWithoutReplacementPMF_head_tail_prob
        baseWeight hbase_nonneg havailable
        forbidden hbudget head₀ q)
  rw [hjoint, hp_prob]
  field_simp [hhead_pos.ne']

/--
Strong tail-conditioning law after a realized head: any conditional probability
whose conditioning and target events both depend only on the tail is the same as
the corresponding conditional probability under the tail sampler.
-/
theorem finiteWithoutReplacementPMF_conditional_tail_event_prob
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (head₀ : {a // a ∉ forbidden})
    (hhead_pos :
      0 < (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega)) head₀).toReal)
    (p q : finiteFreshList α k (insert head₀.1 forbidden) → Prop)
    [DecidablePred p] [DecidablePred q]
    [DecidablePred fun sample : finiteFreshList α (k + 1) forbidden =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
        p (finiteFreshListTailOfHead sample head₀ hhead)]
    [DecidablePred fun sample : finiteFreshList α (k + 1) forbidden =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
        q (finiteFreshListTailOfHead sample head₀ hhead)]
    (hp_pos :
      0 < pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k (insert head₀.1 forbidden)
          (by
            rw [Finset.card_insert_of_notMem head₀.2]
            omega))
        p) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample =>
          ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
            p (finiteFreshListTailOfHead sample head₀ hhead))
        (fun sample =>
          ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
            q (finiteFreshListTailOfHead sample head₀ hhead)) =
      pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k (insert head₀.1 forbidden)
          (by
            rw [Finset.card_insert_of_notMem head₀.2]
            omega))
        p q := by
  classical
  let μ :=
    finiteWithoutReplacementPMF
      baseWeight hbase_nonneg havailable
      (k + 1) forbidden hbudget
  let tailμ :=
    finiteWithoutReplacementPMF
      baseWeight hbase_nonneg havailable
      k (insert head₀.1 forbidden)
      (by
        rw [Finset.card_insert_of_notMem head₀.2]
        omega)
  let lift : (finiteFreshList α k (insert head₀.1 forbidden) → Prop) →
      finiteFreshList α (k + 1) forbidden → Prop :=
    fun event sample =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
        event (finiteFreshListTailOfHead sample head₀ hhead)
  have hp_lift_prob :
      pmfProb μ (lift p) =
        (finiteWeightedPMFAvailable
          baseWeight forbidden hbase_nonneg
          (havailable forbidden (by omega)) head₀).toReal *
          pmfProb tailμ p := by
    simpa [μ, tailμ, lift] using
      (finiteWithoutReplacementPMF_head_tail_prob
        baseWeight hbase_nonneg havailable
        forbidden hbudget head₀ p)
  have hp_lift_pos : 0 < pmfProb μ (lift p) := by
    rw [hp_lift_prob]
    exact mul_pos hhead_pos hp_pos
  have hlift_inter :
      pmfProb μ (fun sample => lift p sample ∧ lift q sample) =
        pmfProb μ (lift fun tail => p tail ∧ q tail) := by
    refine pmfProb_congr μ ?_
    intro sample
    constructor
    · rintro ⟨⟨hphead, hp⟩, ⟨hqhead, hq⟩⟩
      refine ⟨hphead, hp, ?_⟩
      have htail_eq :
          finiteFreshListTailOfHead sample head₀ hqhead =
            finiteFreshListTailOfHead sample head₀ hphead :=
        finiteFreshListTailOfHead_proof_irrel sample head₀ hqhead hphead
      simpa [htail_eq] using hq
    · rintro ⟨hhead, hp, hq⟩
      exact ⟨⟨hhead, hp⟩, ⟨hhead, hq⟩⟩
  have hjoint_inter :
      pmfProb μ (lift fun tail => p tail ∧ q tail) =
        (finiteWeightedPMFAvailable
          baseWeight forbidden hbase_nonneg
          (havailable forbidden (by omega)) head₀).toReal *
          pmfProb tailμ (fun tail => p tail ∧ q tail) := by
    simpa [μ, tailμ, lift] using
      (finiteWithoutReplacementPMF_head_tail_prob
        baseWeight hbase_nonneg havailable
        forbidden hbudget head₀
        (fun tail : finiteFreshList α k (insert head₀.1 forbidden) =>
          p tail ∧ q tail))
  rw [pmfConditionalProb_eq_inter_div_of_pos μ (lift p) (lift q) hp_lift_pos]
  rw [pmfConditionalProb_eq_inter_div_of_pos tailμ p q hp_pos]
  rw [hlift_inter, hjoint_inter, hp_lift_prob]
  field_simp [hhead_pos.ne', hp_pos.ne']

/--
Zero-prefix atom law in prefix-set form.  Positive probability of the
zero-prefix state forces the named previous set to be empty.
-/
theorem finiteWithoutReplacementPMF_zero_prefix_conditional_prob_excluding
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden previous : Finset α)
    (hbudget : forbidden.card + (k + 1) ≤ Fintype.card α)
    (hstate_pos :
      0 < pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample => finiteFreshListPrefixSet 0 sample = previous))
    (havailable_previous :
      0 < finiteAvailableWeight baseWeight (forbidden ∪ previous))
    (next : α) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget)
        (fun sample => finiteFreshListPrefixSet 0 sample = previous)
        (fun sample => sample.1 ⟨0, Nat.succ_pos k⟩ = next) =
      (finiteWeightedPMFExcluding
        baseWeight (forbidden ∪ previous) hbase_nonneg
        havailable_previous next).toReal := by
  classical
  let μ :=
    finiteWithoutReplacementPMF
      baseWeight hbase_nonneg havailable
      (k + 1) forbidden hbudget
  have hprevious_empty : previous = ∅ := by
    rcases
      (pmfProb_pos_iff_exists_pos_mass μ
        (fun sample => finiteFreshListPrefixSet 0 sample = previous)).1
        hstate_pos with
      ⟨sample, hsample, _hmass⟩
    simpa using hsample.symm
  subst previous
  rw [pmfConditionalProb_eq_pmfProb_of_forall_condition]
  · by_cases hnext_forbidden : next ∈ forbidden
    · have hprob_zero :
          pmfProb μ
            (fun sample => sample.1 ⟨0, Nat.succ_pos k⟩ = next) = 0 := by
        exact pmfProb_eq_zero_of_no_mass μ
          (fun sample => sample.1 ⟨0, Nat.succ_pos k⟩ = next)
          (by
            intro sample hsample
            exact False.elim (sample.2.2 ⟨0, Nat.succ_pos k⟩
              (by
                rw [hsample]
                exact hnext_forbidden)))
      rw [hprob_zero]
      have hnext_union : next ∈ forbidden ∪ (∅ : Finset α) := by
        simpa using hnext_forbidden
      rw [finiteWeightedPMFExcluding_apply_toReal_of_mem
        baseWeight (forbidden ∪ (∅ : Finset α)) hbase_nonneg
        havailable_previous hnext_union]
    · rw [finiteWithoutReplacementPMF_head_prob
        (baseWeight := baseWeight)
        (hbase_nonneg := hbase_nonneg)
        (havailable := havailable)
        (forbidden := forbidden)
        (hbudget := hbudget)
        (head₀ := ⟨next, hnext_forbidden⟩)]
      rw [finiteWeightedPMFAvailable_apply_toReal]
      have hnext_union : next ∉ forbidden ∪ (∅ : Finset α) := by
        simpa using hnext_forbidden
      rw [finiteWeightedPMFExcluding_apply_toReal_of_not_mem
        baseWeight (forbidden ∪ (∅ : Finset α)) hbase_nonneg
        havailable_previous hnext_union]
      simp
  · intro sample
    simp

/--
Prefix-set Markov law for the recursive weighted sampler.  Conditional on the
realized set of the first `r` draws, the next draw has the weighted law obtained
by excluding the initial forbidden set together with that realized prefix set.
-/
theorem finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    (r remaining : ℕ) (forbidden previous : Finset α)
    (hbudget : forbidden.card + (remaining + r + 1) ≤ Fintype.card α)
    (hstate_pos :
      0 < pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (remaining + r + 1) forbidden hbudget)
        (fun sample => finiteFreshListPrefixSet r sample = previous))
    (havailable_previous :
      0 < finiteAvailableWeight baseWeight (forbidden ∪ previous))
    (next : α) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (remaining + r + 1) forbidden hbudget)
        (fun sample => finiteFreshListPrefixSet r sample = previous)
        (fun sample => sample.1 ⟨r, by omega⟩ = next) =
      (finiteWeightedPMFExcluding
        baseWeight (forbidden ∪ previous) hbase_nonneg
        havailable_previous next).toReal := by
  classical
  induction r generalizing forbidden previous remaining with
  | zero =>
      simpa using
        (finiteWithoutReplacementPMF_zero_prefix_conditional_prob_excluding
          baseWeight hbase_nonneg havailable
          forbidden previous hbudget hstate_pos havailable_previous next)
  | succ r ih =>
      let μ :=
        finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (remaining + r.succ + 1) forbidden hbudget
      let p : finiteFreshList α (remaining + r.succ + 1) forbidden → Prop :=
        fun sample => finiteFreshListPrefixSet r.succ sample = previous
      let q : finiteFreshList α (remaining + r.succ + 1) forbidden → Prop :=
        fun sample => sample.1 ⟨r.succ, by omega⟩ = next
      let state : finiteFreshList α (remaining + r.succ + 1) forbidden →
          {a // a ∉ forbidden} :=
        fun sample =>
          ⟨sample.1 ⟨0, by omega⟩, sample.2.2 ⟨0, by omega⟩⟩
      refine
        (pmfConditionalProb_eq_of_state_refinement
          (c := (finiteWeightedPMFExcluding
            baseWeight (forbidden ∪ previous) hbase_nonneg
            havailable_previous next).toReal)
          μ p q state
          (by simpa [μ, p] using hstate_pos)
          ?_).trans ?_
      · intro head hspos
        let tailPrefix :
            finiteFreshList α (remaining + r + 1) (insert head.1 forbidden) →
              Prop :=
          fun tail => finiteFreshListPrefixSet r tail = previous.erase head.1
        let tailTarget :
            finiteFreshList α (remaining + r + 1) (insert head.1 forbidden) →
              Prop :=
          fun tail => tail.1 ⟨r, by omega⟩ = next
        let lift : (finiteFreshList α (remaining + r + 1)
              (insert head.1 forbidden) → Prop) →
            finiteFreshList α (remaining + r.succ + 1) forbidden → Prop :=
          fun event sample =>
            ∃ hhead : sample.1 ⟨0, by omega⟩ = head.1,
              event (finiteFreshListTailOfHead sample head hhead)
        have hhead_mem_previous : head.1 ∈ previous := by
          rcases
            (pmfProb_pos_iff_exists_pos_mass μ
              (fun sample => p sample ∧ state sample = head)).1 hspos with
            ⟨sample, hsample, _hmass⟩
          have hfirst_eq : sample.1 ⟨0, by omega⟩ = head.1 := by
            exact congrArg Subtype.val hsample.2
          have hprefix_mem :
              head.1 ∈ finiteFreshListPrefixSet r.succ sample :=
            (finiteFreshList_mem_prefixSet_iff sample head.1).2
              ⟨⟨0, by omega⟩, Nat.succ_pos r, hfirst_eq⟩
          simpa [p, hsample.1] using hprefix_mem
        have hcond_equiv :
            ∀ sample,
              (p sample ∧ state sample = head) ↔ lift tailPrefix sample := by
          intro sample
          constructor
          · rintro ⟨hp, hstate_eq⟩
            have hhead : sample.1 ⟨0, by omega⟩ = head.1 :=
              congrArg Subtype.val hstate_eq
            refine ⟨hhead, ?_⟩
            have hcons :
                finiteFreshListCons head
                    (finiteFreshListTailOfHead sample head hhead) =
                  sample :=
              finiteFreshListCons_tailOfHead sample head hhead
            have hp_cons :
                finiteFreshListPrefixSet r.succ
                    (finiteFreshListCons head
                      (finiteFreshListTailOfHead sample head hhead)) =
                  previous := by
              simpa [hcons] using hp
            exact
              ((finiteFreshListPrefixSet_cons_succ_eq_iff
                head (finiteFreshListTailOfHead sample head hhead)
                previous).1 hp_cons).1
          · rintro ⟨hhead, htail_prefix⟩
            constructor
            · have hcons :
                finiteFreshListCons head
                    (finiteFreshListTailOfHead sample head hhead) =
                  sample :=
                finiteFreshListCons_tailOfHead sample head hhead
              have hp_cons :
                  finiteFreshListPrefixSet r.succ
                      (finiteFreshListCons head
                        (finiteFreshListTailOfHead sample head hhead)) =
                    previous := by
                exact
                  (finiteFreshListPrefixSet_cons_succ_eq_iff
                    head (finiteFreshListTailOfHead sample head hhead)
                    previous).2
                    ⟨htail_prefix, hhead_mem_previous⟩
              simpa [hcons] using hp_cons
            · apply Subtype.ext
              exact hhead
        have htarget_equiv :
            ∀ sample, p sample ∧ state sample = head →
              (q sample ↔ lift tailTarget sample) := by
          intro sample hsample
          have hhead : sample.1 ⟨0, by omega⟩ = head.1 :=
            congrArg Subtype.val hsample.2
          constructor
          · intro hq
            refine ⟨hhead, ?_⟩
            simpa [q, tailTarget, lift, finiteFreshListTailOfHead, finTail]
              using hq
          · rintro ⟨_hhead', htail⟩
            simpa [q, tailTarget, lift, finiteFreshListTailOfHead, finTail]
              using htail
        have hspos_lift :
            0 < pmfProb μ (lift tailPrefix) := by
          rw [← pmfProb_congr μ hcond_equiv]
          exact hspos
        have hlift_prob :
            pmfProb μ (lift tailPrefix) =
              (finiteWeightedPMFAvailable
                baseWeight forbidden hbase_nonneg
                (havailable forbidden (by omega)) head).toReal *
                pmfProb
                  (finiteWithoutReplacementPMF
                    baseWeight hbase_nonneg havailable
                    (remaining + r + 1) (insert head.1 forbidden)
                    (by
                      rw [Finset.card_insert_of_notMem head.2]
                      omega))
                  tailPrefix := by
          simpa [μ, lift, tailPrefix, Nat.succ_eq_add_one, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using
            (finiteWithoutReplacementPMF_head_tail_prob
              baseWeight hbase_nonneg havailable
              forbidden hbudget head tailPrefix)
        have hprod_pos :
            0 <
              (finiteWeightedPMFAvailable
                baseWeight forbidden hbase_nonneg
                (havailable forbidden (by omega)) head).toReal *
                pmfProb
                  (finiteWithoutReplacementPMF
                    baseWeight hbase_nonneg havailable
                    (remaining + r + 1) (insert head.1 forbidden)
                    (by
                      rw [Finset.card_insert_of_notMem head.2]
                      omega))
                  tailPrefix := by
          rwa [hlift_prob] at hspos_lift
        have htail_pos :
            0 < pmfProb
              (finiteWithoutReplacementPMF
                baseWeight hbase_nonneg havailable
                (remaining + r + 1) (insert head.1 forbidden)
                (by
                  rw [Finset.card_insert_of_notMem head.2]
                  omega))
              tailPrefix := by
          exact pos_of_mul_pos_right hprod_pos ENNReal.toReal_nonneg
        have hhead_pos :
            0 < (finiteWeightedPMFAvailable
              baseWeight forbidden hbase_nonneg
              (havailable forbidden (by omega)) head).toReal := by
          exact pos_of_mul_pos_left hprod_pos
            (pmfProb_nonneg
              (finiteWithoutReplacementPMF
                baseWeight hbase_nonneg havailable
                (remaining + r + 1) (insert head.1 forbidden)
                (by
                  rw [Finset.card_insert_of_notMem head.2]
                  omega))
              tailPrefix)
        have htail_cond :
            pmfConditionalProb μ (lift tailPrefix) (lift tailTarget) =
              pmfConditionalProb
                (finiteWithoutReplacementPMF
                  baseWeight hbase_nonneg havailable
                  (remaining + r + 1) (insert head.1 forbidden)
                  (by
                    rw [Finset.card_insert_of_notMem head.2]
                    omega))
                tailPrefix tailTarget := by
          simpa [μ, lift, tailPrefix, tailTarget, Nat.succ_eq_add_one,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (finiteWithoutReplacementPMF_conditional_tail_event_prob
              baseWeight hbase_nonneg havailable
              forbidden hbudget head hhead_pos
              tailPrefix tailTarget htail_pos)
        have hunion :
            (insert head.1 forbidden) ∪ previous.erase head.1 =
              forbidden ∪ previous :=
          finset_insert_union_erase_eq_union_of_mem hhead_mem_previous
        have htail_available :
            0 < finiteAvailableWeight baseWeight
              ((insert head.1 forbidden) ∪ previous.erase head.1) := by
          simpa [hunion] using havailable_previous
        have htail_ind :
            pmfConditionalProb
                (finiteWithoutReplacementPMF
                  baseWeight hbase_nonneg havailable
                  (remaining + r + 1) (insert head.1 forbidden)
                  (by
                    rw [Finset.card_insert_of_notMem head.2]
                    omega))
                tailPrefix tailTarget =
              (finiteWeightedPMFExcluding
                baseWeight ((insert head.1 forbidden) ∪ previous.erase head.1)
                hbase_nonneg htail_available next).toReal := by
          simpa [tailPrefix, tailTarget] using
            (ih (remaining := remaining) (forbidden := insert head.1 forbidden)
              (previous := previous.erase head.1)
              (hbudget := by
                rw [Finset.card_insert_of_notMem head.2]
                omega)
              (hstate_pos := htail_pos)
              (havailable_previous := htail_available)
              )
        calc
          pmfConditionalProb μ (fun sample => p sample ∧ state sample = head) q
              = pmfConditionalProb μ (lift tailPrefix) (lift tailTarget) := by
                exact pmfConditionalProb_congr μ
                  (fun sample => p sample ∧ state sample = head)
                  (lift tailPrefix) q (lift tailTarget)
                  hcond_equiv htarget_equiv
          _ = pmfConditionalProb
                (finiteWithoutReplacementPMF
                  baseWeight hbase_nonneg havailable
                  (remaining + r + 1) (insert head.1 forbidden)
                  (by
                    rw [Finset.card_insert_of_notMem head.2]
                    omega))
                tailPrefix tailTarget := htail_cond
          _ = (finiteWeightedPMFExcluding
                baseWeight ((insert head.1 forbidden) ∪ previous.erase head.1)
                hbase_nonneg htail_available next).toReal := htail_ind
          _ = (finiteWeightedPMFExcluding
                baseWeight (forbidden ∪ previous)
                hbase_nonneg havailable_previous next).toReal := by
                simp [hunion]
      · rfl

/--
Paper-facing wrapper for
`finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding`, with an
arbitrary list length `k` and an explicit decomposition `k = remaining + r + 1`.
-/
theorem finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding_of_length
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    (r remaining k : ℕ) (forbidden previous : Finset α)
    (hr : r < k)
    (hk_length : k = remaining + r + 1)
    (hbudget : forbidden.card + k ≤ Fintype.card α)
    (hstate_pos :
      0 < pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k forbidden hbudget)
        (fun sample => finiteFreshListPrefixSet r sample = previous))
    (havailable_previous :
      0 < finiteAvailableWeight baseWeight (forbidden ∪ previous))
    (next : α) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k forbidden hbudget)
        (fun sample => finiteFreshListPrefixSet r sample = previous)
        (fun sample => sample.1 ⟨r, hr⟩ = next) =
      (finiteWeightedPMFExcluding
        baseWeight (forbidden ∪ previous) hbase_nonneg
        havailable_previous next).toReal := by
  subst k
  simpa using
    (finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding
      baseWeight hbase_nonneg havailable
      r remaining forbidden previous
      (hbudget := hbudget)
      (hstate_pos := hstate_pos)
      (havailable_previous := havailable_previous)
      next)

/--
Ordered-prefix Markov law for the recursive weighted sampler.  Conditional on
the exact ordered first `r` draws, the next draw has the weighted law obtained
by excluding the initial forbidden set together with the realized prefix set.
-/
theorem finiteWithoutReplacementPMF_prefix_conditional_next_prob_excluding
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    (r remaining : ℕ) (forbidden : Finset α)
    (pref : finiteFreshList α r forbidden)
    (hbudget : forbidden.card + (remaining + r + 1) ≤ Fintype.card α)
    (hstate_pos :
      0 < pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (remaining + r + 1) forbidden hbudget)
        (fun sample =>
          finiteFreshListHasPrefix (by omega : r ≤ remaining + r + 1)
            pref sample))
    (havailable_previous :
      0 < finiteAvailableWeight baseWeight
        (forbidden ∪ finiteFreshListPrefixSet r pref))
    (next : α) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (remaining + r + 1) forbidden hbudget)
        (fun sample =>
          finiteFreshListHasPrefix (by omega : r ≤ remaining + r + 1)
            pref sample)
        (fun sample => sample.1 ⟨r, by omega⟩ = next) =
      (finiteWeightedPMFExcluding
        baseWeight (forbidden ∪ finiteFreshListPrefixSet r pref)
        hbase_nonneg havailable_previous next).toReal := by
  classical
  induction r generalizing forbidden remaining with
  | zero =>
      simpa [finiteFreshListHasPrefix] using
        (finiteWithoutReplacementPMF_zero_prefix_conditional_prob_excluding
          baseWeight hbase_nonneg havailable
          forbidden (∅ : Finset α) hbudget
          (hstate_pos := by
            simpa [finiteFreshListHasPrefix] using hstate_pos)
          (havailable_previous := by
            simpa using havailable_previous)
          next)
  | succ r ih =>
      let head : {a // a ∉ forbidden} :=
        ⟨pref.1 ⟨0, Nat.succ_pos r⟩,
          pref.2.2 ⟨0, Nat.succ_pos r⟩⟩
      let tailPrefix : finiteFreshList α r (insert head.1 forbidden) :=
        finiteFreshListTailOfHead pref head rfl
      let μ :=
        finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (remaining + (r + 1) + 1) forbidden hbudget
      let tailμ :=
        finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (remaining + r + 1) (insert head.1 forbidden)
          (by
            rw [Finset.card_insert_of_notMem head.2]
            omega)
      let p : finiteFreshList α (remaining + (r + 1) + 1) forbidden → Prop :=
        fun sample =>
          finiteFreshListHasPrefix
            (by omega : r + 1 ≤ remaining + (r + 1) + 1)
            pref sample
      let q : finiteFreshList α (remaining + (r + 1) + 1) forbidden → Prop :=
        fun sample => sample.1 ⟨r + 1, by omega⟩ = next
      let tailP :
          finiteFreshList α (remaining + r + 1) (insert head.1 forbidden) →
            Prop :=
        fun tail =>
          finiteFreshListHasPrefix
            (by omega : r ≤ remaining + r + 1)
            tailPrefix tail
      let tailQ :
          finiteFreshList α (remaining + r + 1) (insert head.1 forbidden) →
            Prop :=
        fun tail => tail.1 ⟨r, by omega⟩ = next
      let lift :
          (finiteFreshList α (remaining + r + 1)
              (insert head.1 forbidden) → Prop) →
            finiteFreshList α (remaining + (r + 1) + 1) forbidden → Prop :=
        fun event sample =>
          ∃ hhead : sample.1 ⟨0, by omega⟩ = head.1,
            event (finiteFreshListTailOfHead sample head hhead)
      have hcond_equiv : ∀ sample, p sample ↔ lift tailP sample := by
        intro sample
        constructor
        · intro hp
          have hhead : sample.1 ⟨0, by omega⟩ = head.1 := by
            simpa [p, head, finiteFreshListHasPrefix] using
              hp ⟨0, Nat.succ_pos r⟩ (Finset.mem_univ _)
          refine ⟨hhead, ?_⟩
          intro slot _hslot
          have hsucc :
              sample.1 ⟨slot.val.succ, by omega⟩ =
                pref.1 slot.succ := by
            simpa [p, finiteFreshListHasPrefix] using
              hp slot.succ (Finset.mem_univ _)
          simpa [tailP, tailPrefix, finiteFreshListHasPrefix,
            finiteFreshListTailOfHead, finTail] using hsucc
        · rintro ⟨hhead, htail⟩
          intro slot _hslot
          cases slot using Fin.cases with
          | zero =>
              simpa [p, head, finiteFreshListHasPrefix] using hhead
          | succ slot =>
              have htail_slot := htail slot (Finset.mem_univ _)
              simpa [p, tailP, tailPrefix, finiteFreshListHasPrefix,
                finiteFreshListTailOfHead, finTail] using htail_slot
      have htarget_equiv : ∀ sample, p sample → (q sample ↔ lift tailQ sample) := by
        intro sample hp
        have hhead : sample.1 ⟨0, by omega⟩ = head.1 := by
          simpa [p, head, finiteFreshListHasPrefix] using
            hp ⟨0, Nat.succ_pos r⟩ (Finset.mem_univ _)
        constructor
        · intro hq
          refine ⟨hhead, ?_⟩
          simpa [q, tailQ, lift, finiteFreshListTailOfHead, finTail] using hq
        · rintro ⟨_hhead', htail⟩
          simpa [q, tailQ, lift, finiteFreshListTailOfHead, finTail] using htail
      have hp_lift_pos : 0 < pmfProb μ (lift tailP) := by
        rw [← pmfProb_congr μ hcond_equiv]
        simpa [μ, p] using hstate_pos
      have hp_lift_prob :
          pmfProb μ (lift tailP) =
            (finiteWeightedPMFAvailable
              baseWeight forbidden hbase_nonneg
              (havailable forbidden (by omega)) head).toReal *
              pmfProb tailμ tailP := by
        simpa [μ, tailμ, lift, tailP, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          (finiteWithoutReplacementPMF_head_tail_prob
            baseWeight hbase_nonneg havailable
            forbidden hbudget head tailP)
      have hprod_pos :
          0 <
            (finiteWeightedPMFAvailable
              baseWeight forbidden hbase_nonneg
              (havailable forbidden (by omega)) head).toReal *
              pmfProb tailμ tailP := by
        rwa [hp_lift_prob] at hp_lift_pos
      have htail_pos : 0 < pmfProb tailμ tailP := by
        exact pos_of_mul_pos_right hprod_pos ENNReal.toReal_nonneg
      have hhead_pos :
          0 < (finiteWeightedPMFAvailable
            baseWeight forbidden hbase_nonneg
            (havailable forbidden (by omega)) head).toReal := by
        exact pos_of_mul_pos_left hprod_pos
          (pmfProb_nonneg tailμ tailP)
      have htail_cond :
          pmfConditionalProb μ (lift tailP) (lift tailQ) =
            pmfConditionalProb tailμ tailP tailQ := by
        simpa [μ, tailμ, lift, tailP, tailQ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          (finiteWithoutReplacementPMF_conditional_tail_event_prob
            baseWeight hbase_nonneg havailable
            forbidden hbudget head hhead_pos
            tailP tailQ htail_pos)
      have hprefix_cons : finiteFreshListCons head tailPrefix = pref :=
        finiteFreshListCons_tailOfHead pref head rfl
      have hprefix_union :
          (insert head.1 forbidden) ∪ finiteFreshListPrefixSet r tailPrefix =
            forbidden ∪ finiteFreshListPrefixSet (r + 1) pref := by
        rw [← hprefix_cons, finiteFreshListPrefixSet_cons_succ]
        ext a
        by_cases ha_head : a = head.1 <;>
          by_cases ha_forbidden : a ∈ forbidden <;>
          by_cases ha_tail : a ∈ finiteFreshListPrefixSet r tailPrefix <;>
          simp [ha_head, ha_forbidden, ha_tail]
      have htail_available :
          0 < finiteAvailableWeight baseWeight
            ((insert head.1 forbidden) ∪
              finiteFreshListPrefixSet r tailPrefix) := by
        simpa [hprefix_union] using havailable_previous
      have htail_ind :
          pmfConditionalProb tailμ tailP tailQ =
            (finiteWeightedPMFExcluding
              baseWeight
              ((insert head.1 forbidden) ∪
                finiteFreshListPrefixSet r tailPrefix)
              hbase_nonneg htail_available next).toReal := by
        simpa [tailμ, tailP, tailQ] using
          (ih (remaining := remaining) (forbidden := insert head.1 forbidden)
            (pref := tailPrefix)
            (hbudget := by
              rw [Finset.card_insert_of_notMem head.2]
              omega)
            (hstate_pos := by
              simpa [tailμ, tailP] using htail_pos)
            (havailable_previous := htail_available))
      calc
        pmfConditionalProb μ p q
            = pmfConditionalProb μ (lift tailP) (lift tailQ) := by
              exact pmfConditionalProb_congr μ p (lift tailP) q (lift tailQ)
                hcond_equiv htarget_equiv
        _ = pmfConditionalProb tailμ tailP tailQ := htail_cond
        _ =
          (finiteWeightedPMFExcluding
            baseWeight
            ((insert head.1 forbidden) ∪
              finiteFreshListPrefixSet r tailPrefix)
            hbase_nonneg htail_available next).toReal := htail_ind
        _ =
          (finiteWeightedPMFExcluding
            baseWeight
            (forbidden ∪ finiteFreshListPrefixSet (r + 1) pref)
            hbase_nonneg havailable_previous next).toReal := by
            simp [hprefix_union]

/--
Paper-facing wrapper for
`finiteWithoutReplacementPMF_prefix_conditional_next_prob_excluding`, with an
arbitrary list length `k` and an explicit decomposition `k = remaining + r + 1`.
-/
theorem finiteWithoutReplacementPMF_prefix_conditional_next_prob_excluding_of_length
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    (r remaining k : ℕ) (forbidden : Finset α)
    (pref : finiteFreshList α r forbidden)
    (hr : r < k)
    (hk_length : k = remaining + r + 1)
    (hbudget : forbidden.card + k ≤ Fintype.card α)
    (hstate_pos :
      0 < pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k forbidden hbudget)
        (fun sample =>
          finiteFreshListHasPrefix (Nat.le_of_lt hr) pref sample))
    (havailable_previous :
      0 < finiteAvailableWeight baseWeight
        (forbidden ∪ finiteFreshListPrefixSet r pref))
    (next : α) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k forbidden hbudget)
        (fun sample =>
          finiteFreshListHasPrefix (Nat.le_of_lt hr) pref sample)
        (fun sample => sample.1 ⟨r, hr⟩ = next) =
      (finiteWeightedPMFExcluding
        baseWeight (forbidden ∪ finiteFreshListPrefixSet r pref)
        hbase_nonneg havailable_previous next).toReal := by
  subst k
  simpa using
    (finiteWithoutReplacementPMF_prefix_conditional_next_prob_excluding
      baseWeight hbase_nonneg havailable
      r remaining forbidden pref
      (hbudget := hbudget)
      (hstate_pos := hstate_pos)
      (havailable_previous := havailable_previous)
      next)

/--
One positive-prefix atom law: after the first realized draw, the second draw is
distributed as the weighted available draw with the first draw removed.
-/
theorem finiteWithoutReplacementPMF_second_draw_conditional_prob
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 2) ≤ Fintype.card α)
    (head₀ : {a // a ∉ forbidden})
    (hhead_pos :
      0 < (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega)) head₀).toReal)
    (next₀ : {a // a ∉ insert head₀.1 forbidden}) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 2) forbidden hbudget)
        (fun sample => sample.1 ⟨0, by omega⟩ = head₀.1)
        (fun sample => sample.1 ⟨1, by omega⟩ = next₀.1) =
      (finiteWeightedPMFAvailable
        baseWeight (insert head₀.1 forbidden) hbase_nonneg
        (havailable (insert head₀.1 forbidden) (by
          rw [Finset.card_insert_of_notMem head₀.2]
          omega)) next₀).toReal := by
  classical
  let μ :=
    finiteWithoutReplacementPMF
      baseWeight hbase_nonneg havailable
      (k + 2) forbidden hbudget
  let p : finiteFreshList α (k + 2) forbidden → Prop :=
    fun sample => sample.1 ⟨0, by omega⟩ = head₀.1
  let tailTarget : finiteFreshList α (k + 2) forbidden → Prop :=
    fun sample =>
      ∃ hhead : sample.1 ⟨0, Nat.succ_pos (k + 1)⟩ = head₀.1,
        (finiteFreshListTailOfHead sample head₀ hhead).1
          ⟨0, Nat.succ_pos k⟩ = next₀.1
  have htarget_congr :
      pmfConditionalProb μ p
          (fun sample => sample.1 ⟨1, by omega⟩ = next₀.1) =
        pmfConditionalProb μ p tailTarget := by
    exact pmfConditionalProb_congr_of_condition μ p
      (fun sample => sample.1 ⟨1, by omega⟩ = next₀.1)
      tailTarget
      (by
        intro sample hp
        constructor
        · intro hnext
          refine ⟨?_, ?_⟩
          · simpa [p] using hp
          · simpa [tailTarget, finiteFreshListTailOfHead, finTail] using hnext
        · intro htarget
          rcases htarget with ⟨hrealized, hnext⟩
          simpa [tailTarget, finiteFreshListTailOfHead, finTail] using hnext)
  rw [htarget_congr]
  have htail_cond :
      pmfConditionalProb μ p tailTarget =
        pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            (k + 1) (insert head₀.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head₀.2]
              omega))
          (fun tail => tail.1 ⟨0, Nat.succ_pos k⟩ = next₀.1) := by
    simpa [μ, p, tailTarget] using
      (finiteWithoutReplacementPMF_conditional_tail_prob
        baseWeight hbase_nonneg havailable
        forbidden hbudget head₀ hhead_pos
        (fun tail : finiteFreshList α (k + 1) (insert head₀.1 forbidden) =>
          tail.1 ⟨0, Nat.succ_pos k⟩ = next₀.1))
  rw [htail_cond]
  rw [finiteWithoutReplacementPMF_head_prob
    (baseWeight := baseWeight)
    (hbase_nonneg := hbase_nonneg)
    (havailable := havailable)
    (forbidden := insert head₀.1 forbidden)
    (hbudget := by
      rw [Finset.card_insert_of_notMem head₀.2]
      omega)
    (head₀ := next₀)]

/--
One positive-prefix atom law in the ambient type, using the excluding PMF form.
-/
theorem finiteWithoutReplacementPMF_second_draw_conditional_prob_excluding
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + (k + 2) ≤ Fintype.card α)
    (head₀ : {a // a ∉ forbidden})
    (hhead_pos :
      0 < (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg
        (havailable forbidden (by omega)) head₀).toReal)
    (next : α) (hnext : next ∉ insert head₀.1 forbidden) :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 2) forbidden hbudget)
        (fun sample => sample.1 ⟨0, by omega⟩ = head₀.1)
        (fun sample => sample.1 ⟨1, by omega⟩ = next) =
      (finiteWeightedPMFExcluding
        baseWeight (insert head₀.1 forbidden) hbase_nonneg
        (havailable (insert head₀.1 forbidden) (by
          rw [Finset.card_insert_of_notMem head₀.2]
          omega)) next).toReal := by
  classical
  rw [finiteWithoutReplacementPMF_second_draw_conditional_prob
    (baseWeight := baseWeight)
    (hbase_nonneg := hbase_nonneg)
    (havailable := havailable)
    (forbidden := forbidden)
    (hbudget := hbudget)
    (head₀ := head₀)
    (hhead_pos := hhead_pos)
    (next₀ := ⟨next, hnext⟩)]
  rw [finiteWeightedPMFAvailable_apply_toReal]
  rw [finiteWeightedPMFExcluding_apply_toReal_of_not_mem
    baseWeight (insert head₀.1 forbidden) hbase_nonneg
    (havailable (insert head₀.1 forbidden) (by
      rw [Finset.card_insert_of_notMem head₀.2]
      omega)) hnext]

/--
Unnormalized product formula for the atom of a concrete fresh list under the
recursive without-replacement sampler.  Each factor is the chosen atom's base
weight divided by the currently available mass.
-/
noncomputable def finiteFreshListAtomWeight
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) :
    ∀ {k : ℕ} (forbidden : Finset α), finiteFreshList α k forbidden → ℝ
  | 0, _forbidden, _sample => 1
  | k + 1, forbidden, sample =>
      let head : {a // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      (baseWeight head.1 / finiteAvailableWeight baseWeight forbidden) *
        finiteFreshListAtomWeight baseWeight (insert head.1 forbidden) tail
termination_by k forbidden sample => k

/-- Under positive base weights, every concrete ordered fresh list has a
strictly positive recursive atom weight. -/
theorem finiteFreshListAtomWeight_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (hbase_pos : ∀ a, 0 < baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden) :
    ∀ {k : ℕ} (forbidden : Finset α)
      (hbudget : forbidden.card + k ≤ Fintype.card α)
      (sample : finiteFreshList α k forbidden),
      0 < finiteFreshListAtomWeight baseWeight forbidden sample
  | 0, _forbidden, _hbudget, _sample => by
      simp [finiteFreshListAtomWeight]
  | k + 1, forbidden, hbudget, sample => by
      let head : {a // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      rw [finiteFreshListAtomWeight]
      apply mul_pos
      · exact div_pos (hbase_pos head.1) (havailable forbidden (by omega))
      · exact finiteFreshListAtomWeight_pos
          baseWeight hbase_pos havailable (insert head.1 forbidden)
          (by
            rw [Finset.card_insert_of_notMem head.2]
            omega) tail

/--
Atom weights for the recursive without-replacement sampler are invariant under
relabeling when the relabeling preserves weights and transports the forbidden
set.
-/
theorem finiteFreshListAtomWeight_congr_equiv
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (sourceWeight : α → ℝ) (targetWeight : β → ℝ)
    (e : α ≃ β)
    (hweight : ∀ a, targetWeight (e a) = sourceWeight a) :
    ∀ {k : ℕ} {forbidden : Finset α} {targetForbidden : Finset β}
      (hmem : ∀ a, e a ∈ targetForbidden ↔ a ∈ forbidden)
      (sample : finiteFreshList α k forbidden),
      finiteFreshListAtomWeight targetWeight targetForbidden
          (finiteFreshListRelabelEquiv e hmem sample) =
        finiteFreshListAtomWeight sourceWeight forbidden sample
  | 0, forbidden, targetForbidden, hmem, sample => by
      simp [finiteFreshListAtomWeight, finiteFreshListRelabelEquiv]
  | k + 1, forbidden, targetForbidden, hmem, sample => by
      classical
      let sourceHead : {a // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let targetHead : {b // b ∉ targetForbidden} :=
        ⟨e sourceHead.1, by
          intro htarget
          exact sourceHead.2 ((hmem sourceHead.1).1 htarget)⟩
      let sourceTail := finiteFreshListTailOfHead sample sourceHead rfl
      let relabeled := finiteFreshListRelabelEquiv e hmem sample
      have htarget_head :
          relabeled.1 ⟨0, Nat.succ_pos k⟩ = targetHead.1 := by
        rfl
      let targetTail := finiteFreshListTailOfHead relabeled targetHead htarget_head
      have hmem_tail :
          ∀ a, e a ∈ insert targetHead.1 targetForbidden ↔
            a ∈ insert sourceHead.1 forbidden := by
        intro a
        constructor
        · intro ha
          rw [Finset.mem_insert] at ha ⊢
          rcases ha with hea | ha
          · exact Or.inl (e.injective hea)
          · exact Or.inr ((hmem a).1 ha)
        · intro ha
          rw [Finset.mem_insert] at ha ⊢
          rcases ha with ha | ha
          · exact Or.inl (by simpa [sourceHead, targetHead, ha])
          · exact Or.inr ((hmem a).2 ha)
      have htail_eq :
          targetTail = finiteFreshListRelabelEquiv e hmem_tail sourceTail := by
        ext slot
        rfl
      have hrec :=
        finiteFreshListAtomWeight_congr_equiv
          sourceWeight targetWeight e hweight hmem_tail sourceTail
      rw [finiteFreshListAtomWeight, finiteFreshListAtomWeight]
      rw [finiteAvailableWeight_congr_equiv
        sourceWeight targetWeight forbidden targetForbidden e hweight hmem]
      change
        targetWeight targetHead.1 / finiteAvailableWeight sourceWeight forbidden *
            finiteFreshListAtomWeight targetWeight
              (insert targetHead.1 targetForbidden) targetTail =
          sourceWeight sourceHead.1 / finiteAvailableWeight sourceWeight forbidden *
            finiteFreshListAtomWeight sourceWeight
              (insert sourceHead.1 forbidden) sourceTail
      rw [show targetWeight targetHead.1 = sourceWeight sourceHead.1 by
        simp [sourceHead, targetHead, hweight]]
      rw [htail_eq, hrec]

/--
Scaling every base weight by a nonzero constant does not change the atom
weights of the sequential without-replacement law.
-/
theorem finiteFreshListAtomWeight_const_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (c : ℝ) (hc : c ≠ 0) :
    ∀ {k : ℕ} (forbidden : Finset α)
      (sample : finiteFreshList α k forbidden),
      finiteFreshListAtomWeight (fun a => c * baseWeight a) forbidden sample =
        finiteFreshListAtomWeight baseWeight forbidden sample
  | 0, _forbidden, _sample => by
      simp [finiteFreshListAtomWeight]
  | k + 1, forbidden, sample => by
      let head : {a // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      have htail :=
        finiteFreshListAtomWeight_const_mul
          baseWeight c hc (insert head.1 forbidden) tail
      rw [finiteFreshListAtomWeight, finiteFreshListAtomWeight]
      dsimp only
      rw [finiteAvailableWeight_const_mul]
      rw [mul_div_mul_left _ _ hc]
      exact congrArg
        (fun x =>
          (baseWeight head.1 / finiteAvailableWeight baseWeight forbidden) * x)
        htail

/--
Exact atom formula for the recursive without-replacement sampler.
-/
theorem finiteWithoutReplacementPMF_atom_toReal
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden) :
    ∀ {k : ℕ} (forbidden : Finset α)
      (hbudget : forbidden.card + k ≤ Fintype.card α)
      (sample : finiteFreshList α k forbidden),
      ((finiteWithoutReplacementPMF
        baseWeight hbase_nonneg havailable
        k forbidden hbudget) sample).toReal =
        finiteFreshListAtomWeight baseWeight forbidden sample
  | 0, forbidden, hbudget, sample => by
      classical
      have hsample : sample = finiteFreshListNil α forbidden := by
        ext slot
        exact Fin.elim0 slot
      subst sample
      simp [finiteWithoutReplacementPMF, finiteFreshListAtomWeight]
  | k + 1, forbidden, hbudget, sample => by
      classical
      let μ :=
        finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget
      let head : {a // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      let q : finiteFreshList α k (insert head.1 forbidden) → Prop :=
        fun candidate => candidate = tail
      let lifted : finiteFreshList α (k + 1) forbidden → Prop :=
        fun candidate =>
          ∃ hhead : candidate.1 ⟨0, Nat.succ_pos k⟩ = head.1,
            q (finiteFreshListTailOfHead candidate head hhead)
      have hlift_singleton :
          pmfProb μ lifted = pmfProb μ (fun candidate => candidate = sample) := by
        refine pmfProb_congr μ ?_
        intro candidate
        constructor
        · rintro ⟨hhead, htail⟩
          have hcandidate :
              finiteFreshListCons head
                  (finiteFreshListTailOfHead candidate head hhead) =
                candidate :=
            finiteFreshListCons_tailOfHead candidate head hhead
          have hsample :
              finiteFreshListCons head tail = sample :=
            finiteFreshListCons_tailOfHead sample head rfl
          rw [← hcandidate, htail, hsample]
        · intro hcandidate_eq
          subst candidate
          exact ⟨rfl, rfl⟩
      have hhead_tail :
          pmfProb μ lifted =
            (finiteWeightedPMFAvailable
              baseWeight forbidden hbase_nonneg
              (havailable forbidden (by omega)) head).toReal *
              pmfProb
                (finiteWithoutReplacementPMF
                  baseWeight hbase_nonneg havailable
                  k (insert head.1 forbidden)
                  (by
                    rw [Finset.card_insert_of_notMem head.2]
                    omega))
                q := by
        simpa [μ, lifted, q, head, tail] using
          (finiteWithoutReplacementPMF_head_tail_prob
            baseWeight hbase_nonneg havailable
            forbidden hbudget head q)
      have htail_atom :
          ((finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k (insert head.1 forbidden)
            (by
              rw [Finset.card_insert_of_notMem head.2]
              omega)) tail).toReal =
            finiteFreshListAtomWeight baseWeight (insert head.1 forbidden) tail :=
        finiteWithoutReplacementPMF_atom_toReal
          baseWeight hbase_nonneg havailable
          (insert head.1 forbidden)
          (by
            rw [Finset.card_insert_of_notMem head.2]
            omega)
          tail
      calc
        (μ sample).toReal =
            pmfProb μ (fun candidate => candidate = sample) := by
              rw [pmfProb_singleton]
        _ = pmfProb μ lifted := by rw [hlift_singleton]
        _ =
            (finiteWeightedPMFAvailable
              baseWeight forbidden hbase_nonneg
              (havailable forbidden (by omega)) head).toReal *
              pmfProb
                (finiteWithoutReplacementPMF
                  baseWeight hbase_nonneg havailable
                  k (insert head.1 forbidden)
                  (by
                    rw [Finset.card_insert_of_notMem head.2]
                    omega))
                q := hhead_tail
        _ =
            (baseWeight head.1 / finiteAvailableWeight baseWeight forbidden) *
              ((finiteWithoutReplacementPMF
                baseWeight hbase_nonneg havailable
                k (insert head.1 forbidden)
                (by
                  rw [Finset.card_insert_of_notMem head.2]
                  omega)) tail).toReal := by
              rw [finiteWeightedPMFAvailable_apply_toReal]
              rw [pmfProb_singleton]
        _ =
            (baseWeight head.1 / finiteAvailableWeight baseWeight forbidden) *
              finiteFreshListAtomWeight baseWeight (insert head.1 forbidden)
                tail := by
              rw [htail_atom]
        _ = finiteFreshListAtomWeight baseWeight forbidden sample := by
              simp [finiteFreshListAtomWeight, head, tail]

/-- With strictly positive base weights, every admissible ordered fresh list
has strictly positive mass under the without-replacement sampler. -/
theorem finiteWithoutReplacementPMF_atom_toReal_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (hbase_pos : ∀ a, 0 < baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + k ≤ Fintype.card α)
    (sample : finiteFreshList α k forbidden) :
    0 < ((finiteWithoutReplacementPMF
      baseWeight hbase_nonneg havailable k forbidden hbudget) sample).toReal := by
  rw [finiteWithoutReplacementPMF_atom_toReal]
  exact finiteFreshListAtomWeight_pos
    baseWeight hbase_pos havailable forbidden hbudget sample

/--
Event-probability formula for the recursive without-replacement sampler as a
finite sum of the concrete fresh-list atom weights.
-/
theorem finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + k ≤ Fintype.card α)
    (event : finiteFreshList α k forbidden → Prop) [DecidablePred event] :
    pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k forbidden hbudget)
        event =
      ∑ sample : finiteFreshList α k forbidden,
        if event sample then
          finiteFreshListAtomWeight baseWeight forbidden sample
        else 0 := by
  classical
  unfold pmfProb pmfExp
  refine Finset.sum_congr rfl ?_
  intro sample _hsample
  rw [finiteWithoutReplacementPMF_atom_toReal
    baseWeight hbase_nonneg havailable forbidden hbudget sample]
  by_cases hevent : event sample <;> simp [hevent]

/--
Event probabilities for the recursive without-replacement sampler are invariant
under a relabeling that preserves weights, transports forbidden atoms, and
transports the event.
-/
theorem finiteWithoutReplacementPMF_event_prob_congr_equiv
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (sourceWeight : α → ℝ) (targetWeight : β → ℝ)
    (source_nonneg : ∀ a, 0 ≤ sourceWeight a)
    (target_nonneg : ∀ b, 0 ≤ targetWeight b)
    (source_available : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight sourceWeight forbidden)
    (target_available : ∀ forbidden : Finset β,
      forbidden.card < Fintype.card β →
        0 < finiteAvailableWeight targetWeight forbidden)
    {k : ℕ}
    (forbidden : Finset α) (targetForbidden : Finset β)
    (sourceBudget : forbidden.card + k ≤ Fintype.card α)
    (targetBudget : targetForbidden.card + k ≤ Fintype.card β)
    (e : α ≃ β)
    (hweight : ∀ a, targetWeight (e a) = sourceWeight a)
    (hmem : ∀ a, e a ∈ targetForbidden ↔ a ∈ forbidden)
    (sourceEvent : finiteFreshList α k forbidden → Prop)
    (targetEvent : finiteFreshList β k targetForbidden → Prop)
    [DecidablePred sourceEvent] [DecidablePred targetEvent]
    (hevent : ∀ sample,
      targetEvent (finiteFreshListRelabelEquiv e hmem sample) ↔
        sourceEvent sample) :
    pmfProb
        (finiteWithoutReplacementPMF
          targetWeight target_nonneg target_available
          k targetForbidden targetBudget)
        targetEvent =
      pmfProb
        (finiteWithoutReplacementPMF
          sourceWeight source_nonneg source_available
          k forbidden sourceBudget)
        sourceEvent := by
  classical
  let relabel :=
    finiteFreshListRelabelEquiv
      (k := k) (forbidden := forbidden) (targetForbidden := targetForbidden)
      e hmem
  rw [finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight]
  rw [finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight]
  calc
    (∑ sample : finiteFreshList β k targetForbidden,
        if targetEvent sample then
          finiteFreshListAtomWeight targetWeight targetForbidden sample
        else 0)
        =
      (∑ sample : finiteFreshList α k forbidden,
        if targetEvent (relabel sample) then
          finiteFreshListAtomWeight targetWeight targetForbidden (relabel sample)
        else 0) := by
          simpa [relabel] using
            (Equiv.sum_comp relabel
              (fun sample : finiteFreshList β k targetForbidden =>
                if targetEvent sample then
                  finiteFreshListAtomWeight targetWeight targetForbidden sample
                else 0)).symm
    _ = (∑ sample : finiteFreshList α k forbidden,
        if sourceEvent sample then
          finiteFreshListAtomWeight sourceWeight forbidden sample
        else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sample _hsample
          by_cases hsource : sourceEvent sample
          · have htarget : targetEvent (relabel sample) :=
              (hevent sample).2 hsource
            simp [hsource, htarget, relabel,
              finiteFreshListAtomWeight_congr_equiv
                sourceWeight targetWeight e hweight hmem sample]
          · have htarget : ¬ targetEvent (relabel sample) := by
              intro htarget
              exact hsource ((hevent sample).1 htarget)
            simp [hsource, htarget]

/--
Scaling all base weights by a positive constant does not change any event
probability for the recursive weighted without-replacement sampler.
-/
theorem finiteWithoutReplacementPMF_event_prob_const_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (c : ℝ) (hc : 0 < c)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + k ≤ Fintype.card α)
    (event : finiteFreshList α k forbidden → Prop) [DecidablePred event] :
    pmfProb
        (finiteWithoutReplacementPMF
          (fun a => c * baseWeight a)
          (fun a => mul_nonneg hc.le (hbase_nonneg a))
          (fun forbidden hcard => by
            rw [finiteAvailableWeight_const_mul]
            exact mul_pos hc (havailable forbidden hcard))
          k forbidden hbudget)
        event =
      pmfProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k forbidden hbudget)
        event := by
  classical
  rw [finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight]
  rw [finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight]
  refine Finset.sum_congr rfl ?_
  intro sample _hsample
  by_cases hevent : event sample <;>
    simp [hevent,
      finiteFreshListAtomWeight_const_mul baseWeight c hc.ne']

/--
Scaling all base weights by a positive constant also leaves conditional event
probabilities unchanged for the recursive without-replacement sampler.
-/
theorem finiteWithoutReplacementPMF_conditional_prob_const_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (c : ℝ) (hc : 0 < c)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + k ≤ Fintype.card α)
    (condition event : finiteFreshList α k forbidden → Prop)
    [DecidablePred condition] [DecidablePred event] :
    pmfConditionalProb
        (finiteWithoutReplacementPMF
          (fun a => c * baseWeight a)
          (fun a => mul_nonneg hc.le (hbase_nonneg a))
          (fun forbidden hcard => by
            rw [finiteAvailableWeight_const_mul]
            exact mul_pos hc (havailable forbidden hcard))
          k forbidden hbudget)
        condition event =
      pmfConditionalProb
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          k forbidden hbudget)
        condition event := by
  classical
  let μscaled :=
    finiteWithoutReplacementPMF
      (fun a => c * baseWeight a)
      (fun a => mul_nonneg hc.le (hbase_nonneg a))
      (fun forbidden hcard => by
        rw [finiteAvailableWeight_const_mul]
        exact mul_pos hc (havailable forbidden hcard))
      k forbidden hbudget
  let μbase :=
    finiteWithoutReplacementPMF
      baseWeight hbase_nonneg havailable k forbidden hbudget
  have hcondition :
      pmfProb μscaled condition = pmfProb μbase condition := by
    simpa [μscaled, μbase] using
      finiteWithoutReplacementPMF_event_prob_const_mul
        baseWeight c hc hbase_nonneg havailable forbidden hbudget condition
  by_cases hzero : pmfProb μbase condition = 0
  · have hzero_scaled : pmfProb μscaled condition = 0 := by
      rw [hcondition, hzero]
    simp [pmfConditionalProb, pmfConditionalExp, hzero, hzero_scaled,
      μscaled, μbase]
  · have hpos : 0 < pmfProb μbase condition :=
      lt_of_le_of_ne (pmfProb_nonneg μbase condition) (Ne.symm hzero)
    have hpos_scaled : 0 < pmfProb μscaled condition := by
      rw [hcondition]
      exact hpos
    rw [pmfConditionalProb_eq_inter_div_of_pos μscaled condition event
      hpos_scaled]
    rw [pmfConditionalProb_eq_inter_div_of_pos μbase condition event hpos]
    have hinter :
        pmfProb μscaled (fun sample => condition sample ∧ event sample) =
          pmfProb μbase (fun sample => condition sample ∧ event sample) := by
      simpa [μscaled, μbase] using
        finiteWithoutReplacementPMF_event_prob_const_mul
          baseWeight c hc hbase_nonneg havailable forbidden hbudget
          (fun sample : finiteFreshList α k forbidden =>
            condition sample ∧ event sample)
    rw [hinter, hcondition]

/--
Available mass is continuous under pointwise convergence of the finite base
weight vector.
-/
theorem finiteAvailableWeight_tendsto
    {α : Type*} [Fintype α] [DecidableEq α]
    (weightSeq : ℕ → α → ℝ) (baseWeight : α → ℝ)
    (hweight : ∀ a : α,
      Filter.Tendsto (fun scale : ℕ => weightSeq scale a)
        Filter.atTop (nhds (baseWeight a)))
    (forbidden : Finset α) :
    Filter.Tendsto
      (fun scale : ℕ => finiteAvailableWeight (weightSeq scale) forbidden)
      Filter.atTop
      (nhds (finiteAvailableWeight baseWeight forbidden)) := by
  classical
  unfold finiteAvailableWeight
  refine tendsto_finset_sum (Finset.univ : Finset α) ?_
  intro a _ha_univ
  by_cases ha : a ∈ forbidden
  · simpa [ha] using (Filter.tendsto_const_nhds (x := (0 : ℝ)))
  · simpa [ha] using hweight a

/--
For a fixed fresh list, its atom-weight product is continuous under pointwise
convergence of the base weight vector, as long as the limiting sampler has
positive available mass along the realized prefixes.
-/
theorem finiteFreshListAtomWeight_tendsto
    {α : Type*} [Fintype α] [DecidableEq α]
    (weightSeq : ℕ → α → ℝ) (baseWeight : α → ℝ)
    (hweight : ∀ a : α,
      Filter.Tendsto (fun scale : ℕ => weightSeq scale a)
        Filter.atTop (nhds (baseWeight a)))
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden) :
    ∀ {k : ℕ} (forbidden : Finset α)
      (hbudget : forbidden.card + k ≤ Fintype.card α)
      (sample : finiteFreshList α k forbidden),
      Filter.Tendsto
        (fun scale : ℕ =>
          finiteFreshListAtomWeight (weightSeq scale) forbidden sample)
        Filter.atTop
        (nhds (finiteFreshListAtomWeight baseWeight forbidden sample))
  | 0, _forbidden, _hbudget, _sample => by
      simp [finiteFreshListAtomWeight]
  | k + 1, forbidden, hbudget, sample => by
      classical
      let head : {a // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      have hnum :
          Filter.Tendsto
            (fun scale : ℕ => weightSeq scale head.1)
            Filter.atTop (nhds (baseWeight head.1)) :=
        hweight head.1
      have hden :
          Filter.Tendsto
            (fun scale : ℕ =>
              finiteAvailableWeight (weightSeq scale) forbidden)
            Filter.atTop
            (nhds (finiteAvailableWeight baseWeight forbidden)) :=
        finiteAvailableWeight_tendsto weightSeq baseWeight hweight forbidden
      have hden_ne :
          finiteAvailableWeight baseWeight forbidden ≠ 0 :=
        ne_of_gt (havailable forbidden (by omega))
      have hfactor :
          Filter.Tendsto
            (fun scale : ℕ =>
              weightSeq scale head.1 /
                finiteAvailableWeight (weightSeq scale) forbidden)
            Filter.atTop
            (nhds
              (baseWeight head.1 /
                finiteAvailableWeight baseWeight forbidden)) :=
        hnum.div hden hden_ne
      have htail_budget :
          (insert head.1 forbidden).card + k ≤ Fintype.card α := by
        rw [Finset.card_insert_of_notMem head.2]
        omega
      have htail :
          Filter.Tendsto
            (fun scale : ℕ =>
              finiteFreshListAtomWeight (weightSeq scale)
                (insert head.1 forbidden) tail)
            Filter.atTop
            (nhds
              (finiteFreshListAtomWeight baseWeight
                (insert head.1 forbidden) tail)) :=
        finiteFreshListAtomWeight_tendsto
          weightSeq baseWeight hweight havailable
          (insert head.1 forbidden) htail_budget tail
      have hmul := hfactor.mul htail
      simpa [finiteFreshListAtomWeight, head, tail] using hmul

/--
Any fixed event under the recursive without-replacement sampler has a
probability that is continuous under pointwise convergence of the finite base
weight vector.
-/
theorem finiteWithoutReplacementPMF_event_prob_tendsto
    {α : Type*} [Fintype α] [DecidableEq α]
    (weightSeq : ℕ → α → ℝ) (baseWeight : α → ℝ)
    (hseq_nonneg : ∀ scale a, 0 ≤ weightSeq scale a)
    (hseq_available : ∀ scale, ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight (weightSeq scale) forbidden)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (hbase_available : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    (hweight : ∀ a : α,
      Filter.Tendsto (fun scale : ℕ => weightSeq scale a)
        Filter.atTop (nhds (baseWeight a)))
    {k : ℕ} (forbidden : Finset α)
    (hbudget : forbidden.card + k ≤ Fintype.card α)
    (event : finiteFreshList α k forbidden → Prop) [DecidablePred event] :
    Filter.Tendsto
      (fun scale : ℕ =>
        pmfProb
          (finiteWithoutReplacementPMF
            (weightSeq scale) (hseq_nonneg scale)
            (hseq_available scale) k forbidden hbudget)
          event)
      Filter.atTop
      (nhds
        (pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg hbase_available
            k forbidden hbudget)
          event)) := by
  classical
  have hsum :
      Filter.Tendsto
        (fun scale : ℕ =>
          ∑ sample : finiteFreshList α k forbidden,
            if event sample then
              finiteFreshListAtomWeight (weightSeq scale) forbidden sample
            else 0)
        Filter.atTop
        (nhds
          (∑ sample : finiteFreshList α k forbidden,
            if event sample then
              finiteFreshListAtomWeight baseWeight forbidden sample
            else 0)) := by
    refine tendsto_finset_sum
      (Finset.univ : Finset (finiteFreshList α k forbidden)) ?_
    intro sample _hsample
    by_cases hevent : event sample
    · simpa [hevent] using
        finiteFreshListAtomWeight_tendsto
          weightSeq baseWeight hweight hbase_available
          forbidden hbudget sample
    · simpa [hevent] using (Filter.tendsto_const_nhds (x := (0 : ℝ)))
  rw [finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight
    baseWeight hbase_nonneg hbase_available forbidden hbudget event]
  exact hsum.congr fun scale => by
    exact
      (finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight
        (weightSeq scale) (hseq_nonneg scale) (hseq_available scale)
        forbidden hbudget event).symm

/--
Positive probability of omitting a fixed atom from a without-replacement draw.
If there is room to draw `k` elements while also excluding `a`, and all base
weights are strictly positive, then the event that the whole fresh list avoids
`a` has positive probability.
-/
theorem finiteWithoutReplacementPMF_omit_atom_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (hbase_pos : ∀ a, 0 < baseWeight a)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden) :
    ∀ {k : ℕ} (forbidden : Finset α)
      (hbudget : forbidden.card + k ≤ Fintype.card α) (a : α),
      a ∉ forbidden →
      forbidden.card + k < Fintype.card α →
        0 < pmfProb
          (finiteWithoutReplacementPMF
            baseWeight hbase_nonneg havailable
            k forbidden hbudget)
          (fun sample => ∀ slot : Fin k, sample.1 slot ≠ a)
  | 0, forbidden, hbudget, a, _ha_not_forbidden, _hroom => by
      classical
      have htrue :
          ∀ sample : finiteFreshList α 0 forbidden,
            ∀ slot : Fin 0, sample.1 slot ≠ a := by
        intro _sample slot
        exact Fin.elim0 slot
      rw [pmfProb_eq_one_of_forall
        (finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          0 forbidden hbudget)
        (fun sample : finiteFreshList α 0 forbidden =>
          ∀ slot : Fin 0, sample.1 slot ≠ a)
        htrue]
      norm_num
  | k + 1, forbidden, hbudget, a, ha_not_forbidden, hroom => by
      classical
      have hinsert_card :
          (insert a forbidden).card < Fintype.card α := by
        rw [Finset.card_insert_of_notMem ha_not_forbidden]
        omega
      obtain ⟨headVal, _hhead_univ, hhead_not_insert⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card
          (s := insert a forbidden) (t := (Finset.univ : Finset α))
          (by
            simpa [Finset.card_univ] using hinsert_card)
      have hhead_not_forbidden : headVal ∉ forbidden := by
        intro hmem
        exact hhead_not_insert (by simp [hmem])
      have hhead_ne_a : headVal ≠ a := by
        intro h
        exact hhead_not_insert (by simp [h])
      let head₀ : {x // x ∉ forbidden} := ⟨headVal, hhead_not_forbidden⟩
      let tailForbidden : Finset α := insert headVal forbidden
      have htail_budget :
          tailForbidden.card + k ≤ Fintype.card α := by
        simp [tailForbidden, Finset.card_insert_of_notMem hhead_not_forbidden]
        omega
      have htail_room :
          tailForbidden.card + k < Fintype.card α := by
        simp [tailForbidden, Finset.card_insert_of_notMem hhead_not_forbidden]
        omega
      have ha_tail : a ∉ tailForbidden := by
        simp [tailForbidden, ha_not_forbidden, hhead_ne_a.symm]
      let q : finiteFreshList α k tailForbidden → Prop :=
        fun tail => ∀ slot : Fin k, tail.1 slot ≠ a
      have htail_pos :
          0 < pmfProb
            (finiteWithoutReplacementPMF
              baseWeight hbase_nonneg havailable
              k tailForbidden htail_budget)
            q := by
        simpa [q, tailForbidden, htail_budget] using
          (finiteWithoutReplacementPMF_omit_atom_pos
            baseWeight hbase_nonneg hbase_pos havailable
            tailForbidden htail_budget a ha_tail htail_room)
      have hhead_pos :
          0 <
            (finiteWeightedPMFAvailable
              baseWeight forbidden hbase_nonneg
              (havailable forbidden (by omega)) head₀).toReal := by
        rw [finiteWeightedPMFAvailable_apply_toReal]
        exact div_pos (hbase_pos headVal) (havailable forbidden (by omega))
      let μ :=
        finiteWithoutReplacementPMF
          baseWeight hbase_nonneg havailable
          (k + 1) forbidden hbudget
      let joint : finiteFreshList α (k + 1) forbidden → Prop :=
        fun sample =>
          ∃ hhead : sample.1 ⟨0, Nat.succ_pos k⟩ = head₀.1,
            q (finiteFreshListTailOfHead sample head₀ hhead)
      let omitted : finiteFreshList α (k + 1) forbidden → Prop :=
        fun sample => ∀ slot : Fin (k + 1), sample.1 slot ≠ a
      have hjoint_prob :
          pmfProb μ joint =
            (finiteWeightedPMFAvailable
              baseWeight forbidden hbase_nonneg
              (havailable forbidden (by omega)) head₀).toReal *
              pmfProb
                (finiteWithoutReplacementPMF
                  baseWeight hbase_nonneg havailable
                  k (insert head₀.1 forbidden)
                  (by
                    rw [Finset.card_insert_of_notMem head₀.2]
                    omega))
                q := by
        simpa [μ, joint, q, head₀, tailForbidden] using
          (finiteWithoutReplacementPMF_head_tail_prob
            baseWeight hbase_nonneg havailable
            forbidden hbudget head₀ q)
      have hjoint_pos : 0 < pmfProb μ joint := by
        rw [hjoint_prob]
        exact mul_pos hhead_pos (by simpa [q, tailForbidden] using htail_pos)
      have hjoint_le_omitted : pmfProb μ joint ≤ pmfProb μ omitted := by
        refine pmfProb_le_of_imp μ joint omitted ?_
        intro sample hsample slot
        rcases hsample with ⟨hhead, htail⟩
        cases slot using Fin.cases with
        | zero =>
            intro hsample_eq_a
            exact hhead_ne_a (hhead.symm.trans hsample_eq_a)
        | succ slot =>
            have htail_slot := htail slot
            simpa [q, finiteFreshListTailOfHead, finTail] using htail_slot
      exact lt_of_lt_of_le hjoint_pos
        (by simpa [μ, omitted] using hjoint_le_omitted)

end AppliedModelingLib
