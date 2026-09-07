import AppliedModelingLib.Foundations.Math.SimplexRounding
import AppliedModelingLib.Foundations.Probability.FiniteProductMultinomialCounts

open scoped BigOperators
open Filter

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Empirical multinomial count events

This file isolates the finite iid mass calculation for empirical count
vectors.  The main unconditional theorem proves the exact multinomial
probability formula for a prescribed empirical type.
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The finite set of samples whose empirical counts are the prescribed vector. -/
def empiricalCountEventFinset (n : ℕ) (k : α → ℕ) :
    Finset (Fin n → α) :=
  (Finset.univ : Finset (Fin n → α)).filter
    (fun sample : Fin n → α => ∀ a : α, empiricalCount sample a = k a)

@[simp]
theorem mem_empiricalCountEventFinset
    {n : ℕ} {k : α → ℕ} {sample : Fin n → α} :
    sample ∈ empiricalCountEventFinset (α := α) n k ↔
      ∀ a : α, empiricalCount sample a = k a := by
  simp [empiricalCountEventFinset]

private def empiricalCountEventOnFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (k : α → ℕ) :
    Finset (ι → α) :=
  (Finset.univ : Finset (ι → α)).filter
    (fun sample : ι → α =>
      (∀ i : ι, sample i ∈ s) ∧
        ∀ a : α, a ∈ s → empiricalCount sample a = k a)

@[simp]
private theorem mem_empiricalCountEventOnFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset α} {k : α → ℕ} {sample : ι → α} :
    sample ∈ empiricalCountEventOnFinset (α := α) s k ↔
      (∀ i : ι, sample i ∈ s) ∧
        ∀ a : α, a ∈ s → empiricalCount sample a = k a := by
  simp [empiricalCountEventOnFinset]

private def labelFiber
    {ι : Type*} [Fintype ι] (a : α) (sample : ι → α) :
    Finset ι :=
  (Finset.univ : Finset ι).filter (fun i => sample i = a)

private theorem mem_labelFiber
    {ι : Type*} [Fintype ι] {a : α} {sample : ι → α} {i : ι} :
    i ∈ labelFiber (α := α) a sample ↔ sample i = a := by
  simp [labelFiber]

private theorem empiricalCount_eq_card_labelFiber
    {ι : Type*} [Fintype ι]
    (sample : ι → α) (a : α) :
    empiricalCount sample a = (labelFiber (α := α) a sample).card := by
  rfl

private theorem empiricalCount_eq_list_count_ofFn
    {n : ℕ} (sample : Fin n → α) (a : α) :
    empiricalCount sample a = (List.ofFn sample).count a := by
  classical
  simpa [empiricalCount, successIndexSet, List.Vector.toList_ofFn,
    List.Vector.get_ofFn] using
    (Fin.card_filter_univ_eq_vector_get_eq_count
      (n := n) a (List.Vector.ofFn sample))

private def extendByLabel
    {ι : Type*} [DecidableEq ι] (a : α) (U : Finset ι)
    (rest : {i : ι // i ∉ U} → α) : ι → α :=
  fun i => if h : i ∈ U then a else rest ⟨i, h⟩

private theorem empiricalCount_restrict_compl_eq_of_labelFiber_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {sample : ι → α} {a b : α} {U : Finset ι}
    (hU : labelFiber (α := α) a sample = U) (hba : b ≠ a) :
    empiricalCount (fun i : {i : ι // i ∉ U} => sample i.1) b =
      empiricalCount sample b := by
  classical
  rw [empiricalCount_eq_card_labelFiber, empiricalCount_eq_card_labelFiber]
  refine
    Finset.card_bij
      (s := labelFiber (α := α) b
        (fun i : {i : ι // i ∉ U} => sample i.1))
      (t := labelFiber (α := α) b sample)
      (fun i _hi => i.1) ?_ ?_ ?_
  · intro i hi
    rw [mem_labelFiber] at hi ⊢
    exact hi
  · intro i _hi j _hj hij
    exact Subtype.ext hij
  · intro i hi
    rw [mem_labelFiber] at hi
    have hi_not_mem : i ∉ U := by
      intro hiU
      have hia : sample i = a := by
        have : i ∈ labelFiber (α := α) a sample := by
          simpa [hU] using hiU
        rw [mem_labelFiber] at this
        exact this
      exact hba (hi.symm.trans hia)
    refine ⟨⟨i, hi_not_mem⟩, ?_, rfl⟩
    rw [mem_labelFiber]
    exact hi

private theorem labelFiber_extendByLabel_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset α} {a : α} (ha : a ∉ s)
    (U : Finset ι) (rest : {i : ι // i ∉ U} → α)
    (hrest_mem : ∀ i, rest i ∈ s) :
    labelFiber (α := α) a (extendByLabel (α := α) a U rest) = U := by
  classical
  ext i
  constructor
  · intro hi
    rw [mem_labelFiber] at hi
    by_cases hmem : i ∈ U
    · exact hmem
    · simp [extendByLabel, hmem] at hi
      have hmems : rest ⟨i, hmem⟩ ∈ s := hrest_mem ⟨i, hmem⟩
      rw [hi] at hmems
      exact False.elim (ha hmems)
  · intro hi
    rw [mem_labelFiber]
    simp [extendByLabel, hi]

private theorem empiricalCount_extendByLabel_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset α} {a : α} (ha : a ∉ s)
    (U : Finset ι) (rest : {i : ι // i ∉ U} → α)
    (hrest_mem : ∀ i, rest i ∈ s) :
    empiricalCount (extendByLabel (α := α) a U rest) a = U.card := by
  rw [empiricalCount_eq_card_labelFiber,
    labelFiber_extendByLabel_self (α := α) ha U rest hrest_mem]

private theorem empiricalCount_extendByLabel_of_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset α} {a b : α} (ha : a ∉ s) (hb : b ∈ s)
    (U : Finset ι) (rest : {i : ι // i ∉ U} → α)
    (hrest_mem : ∀ i, rest i ∈ s) :
    empiricalCount (extendByLabel (α := α) a U rest) b =
      empiricalCount rest b := by
  classical
  have hba : b ≠ a := fun h => ha (h ▸ hb)
  have hU :
      labelFiber (α := α) a (extendByLabel (α := α) a U rest) = U :=
    labelFiber_extendByLabel_self (α := α) ha U rest hrest_mem
  have hrestrict :
      (fun i : {i : ι // i ∉ U} =>
        extendByLabel (α := α) a U rest i.1) = rest := by
    funext i
    simp [extendByLabel, i.2]
  calc
    empiricalCount (extendByLabel (α := α) a U rest) b
        =
        empiricalCount
          (fun i : {i : ι // i ∉ U} =>
            extendByLabel (α := α) a U rest i.1) b := by
          exact
            (empiricalCount_restrict_compl_eq_of_labelFiber_eq
              (α := α) (sample := extendByLabel (α := α) a U rest)
              (a := a) (b := b) (U := U) hU hba).symm
    _ = empiricalCount rest b := by
          rw [hrestrict]

private theorem empiricalCountEventOnFinset_fiber_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset α} {a : α} (ha : a ∉ s)
    (k : α → ℕ) (U : Finset ι) (hUcard : U.card = k a) :
    ((empiricalCountEventOnFinset (α := α) (insert a s) k).filter
        (fun sample : ι → α => labelFiber (α := α) a sample = U)).card =
      (empiricalCountEventOnFinset
        (α := α) (ι := {i : ι // i ∉ U}) s k).card := by
  classical
  let A :=
    (empiricalCountEventOnFinset (α := α) (ι := ι) (insert a s) k).filter
      (fun sample : ι → α => labelFiber (α := α) a sample = U)
  let B :=
    empiricalCountEventOnFinset (α := α) (ι := {i : ι // i ∉ U}) s k
  change A.card = B.card
  refine
    Finset.card_bij'
      (s := A) (t := B)
      (fun sample _hsample => fun i : {i : ι // i ∉ U} => sample i.1)
      (fun rest _hrest => extendByLabel (α := α) a U rest)
      ?_ ?_ ?_ ?_
  · intro sample hsample
    dsimp [A] at hsample
    rw [Finset.mem_filter] at hsample
    rcases hsample with ⟨hsample_event, hfiber⟩
    rw [mem_empiricalCountEventOnFinset] at hsample_event ⊢
    constructor
    · intro i
      have hmem_insert : sample i.1 ∈ insert a s := hsample_event.1 i.1
      have hne : sample i.1 ≠ a := by
        intro h
        have hi_fiber : i.1 ∈ labelFiber (α := α) a sample := by
          rw [mem_labelFiber]
          exact h
        exact i.2 (by simpa [hfiber] using hi_fiber)
      exact (Finset.mem_insert.mp hmem_insert).resolve_left hne
    · intro b hb
      have hba : b ≠ a := fun h => ha (h ▸ hb)
      rw [empiricalCount_restrict_compl_eq_of_labelFiber_eq
        (α := α) (sample := sample) (a := a) (b := b) (U := U)
        hfiber hba]
      exact hsample_event.2 b (Finset.mem_insert_of_mem hb)
  · intro rest hrest
    dsimp [B] at hrest
    rw [mem_empiricalCountEventOnFinset] at hrest
    dsimp [A]
    rw [Finset.mem_filter, mem_empiricalCountEventOnFinset]
    have hrest_mem : ∀ i, rest i ∈ s := hrest.1
    constructor
    · constructor
      · intro i
        by_cases hi : i ∈ U
        · simp [extendByLabel, hi]
        · have hvalue :
              extendByLabel (α := α) a U rest i = rest ⟨i, hi⟩ := by
            simp [extendByLabel, hi]
          rw [hvalue]
          exact Finset.mem_insert_of_mem (hrest.1 ⟨i, hi⟩)
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hbs
        · rw [empiricalCount_extendByLabel_self (α := α) ha U rest hrest_mem,
            hUcard]
        · rw [empiricalCount_extendByLabel_of_mem
            (α := α) ha hbs U rest hrest_mem]
          exact hrest.2 b hbs
    · exact labelFiber_extendByLabel_self (α := α) ha U rest hrest_mem
  · intro sample hsample
    dsimp [A] at hsample
    rw [Finset.mem_filter] at hsample
    rcases hsample with ⟨_hsample_event, hfiber⟩
    funext i
    by_cases hi : i ∈ U
    · have hia : sample i = a := by
        have : i ∈ labelFiber (α := α) a sample := by
          simpa [hfiber] using hi
        rw [mem_labelFiber] at this
        exact this
      simp [extendByLabel, hi, hia]
    · simp [extendByLabel, hi]
  · intro rest hrest
    funext i
    simp [extendByLabel, i.2]

/--
Cardinality of finite samples with prescribed empirical counts over a label
finset.  The proof partitions by the fiber of a newly inserted label and then
uses the complement-domain bijection above.
-/
private theorem empiricalCountEventOnFinset_card_eq_multinomial
    (s : Finset α) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (k : α → ℕ),
      (∑ a ∈ s, k a = Fintype.card ι) →
        (empiricalCountEventOnFinset (α := α) (ι := ι) s k).card =
          Nat.multinomial s k := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro ι _ _ k hsum
      have hcard0 : Fintype.card ι = 0 := by
        simpa using hsum.symm
      letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard0
      have hevent :
          empiricalCountEventOnFinset (α := α) (ι := ι) (∅ : Finset α) k =
            Finset.univ := by
        ext sample
        simp [empiricalCountEventOnFinset]
      rw [hevent, Finset.card_univ, Fintype.card_fun, hcard0, pow_zero,
        Nat.multinomial_empty]
  | insert a s ha ih =>
      intro ι _ _ k hsum
      let E : Finset (ι → α) :=
        empiricalCountEventOnFinset (α := α) (ι := ι) (insert a s) k
      let fibers : Finset (Finset ι) :=
        Finset.powersetCard (k a) (Finset.univ : Finset ι)
      have hcover :
          E =
            fibers.biUnion
              (fun U : Finset ι =>
                E.filter
                  (fun sample : ι → α =>
                    labelFiber (α := α) a sample = U)) := by
        ext sample
        constructor
        · intro hsample
          have hsample_event :
              sample ∈
                empiricalCountEventOnFinset
                  (α := α) (ι := ι) (insert a s) k := by
            simpa [E] using hsample
          rw [mem_empiricalCountEventOnFinset] at hsample_event
          have hfiber_card :
              (labelFiber (α := α) a sample).card = k a := by
            rw [← empiricalCount_eq_card_labelFiber sample a]
            exact hsample_event.2 a (Finset.mem_insert_self a s)
          rw [Finset.mem_biUnion]
          refine ⟨labelFiber (α := α) a sample, ?_, ?_⟩
          · change
              labelFiber (α := α) a sample ∈
                Finset.powersetCard (k a) (Finset.univ : Finset ι)
            exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hfiber_card⟩
          · rw [Finset.mem_filter]
            exact ⟨hsample, rfl⟩
        · intro hsample
          rw [Finset.mem_biUnion] at hsample
          rcases hsample with ⟨U, _hU, hsampleU⟩
          exact (Finset.mem_filter.mp hsampleU).1
      have hdisj :
          (↑fibers : Set (Finset ι)).PairwiseDisjoint
            (fun U : Finset ι =>
              E.filter
                (fun sample : ι → α =>
                  labelFiber (α := α) a sample = U)) := by
        rw [Finset.pairwiseDisjoint_iff]
        intro U _hU V _hV hnonempty
        rcases hnonempty with ⟨sample, hsample⟩
        rw [Finset.mem_inter] at hsample
        have hU :
            labelFiber (α := α) a sample = U :=
          (Finset.mem_filter.mp hsample.1).2
        have hV :
            labelFiber (α := α) a sample = V :=
          (Finset.mem_filter.mp hsample.2).2
        exact hU.symm.trans hV
      have htotal :
          k a + ∑ x ∈ s, k x = Fintype.card ι := by
        simpa [Finset.sum_insert ha] using hsum
      have hfiber_card :
          ∀ U ∈ fibers,
            (E.filter
              (fun sample : ι → α =>
                labelFiber (α := α) a sample = U)).card =
              Nat.multinomial s k := by
        intro U hU
        have hUmem :
            U ∈ Finset.powersetCard (k a) (Finset.univ : Finset ι) := by
          simpa only [fibers] using hU
        have hUcard : U.card = k a :=
          (Finset.mem_powersetCard.mp hUmem).2
        have hsum_sub :
            ∑ x ∈ s, k x = Fintype.card ι - k a :=
          Nat.eq_sub_of_add_eq (by
            simpa [Nat.add_comm] using htotal)
        have hcompl_card :
            Fintype.card {i : ι // i ∉ U} =
              Fintype.card ι - k a := by
          calc
            Fintype.card {i : ι // i ∉ U}
                =
                Fintype.card ι - Fintype.card {i : ι // i ∈ U} := by
                  exact Fintype.card_subtype_compl
                    (p := fun i : ι => i ∈ U)
            _ = Fintype.card ι - U.card := by
                  rw [Fintype.card_coe U]
            _ = Fintype.card ι - k a := by
                  rw [hUcard]
        have hsum_compl :
            ∑ x ∈ s, k x = Fintype.card {i : ι // i ∉ U} := by
          rw [hsum_sub, hcompl_card]
        have hfiber :
            (E.filter
              (fun sample : ι → α =>
                labelFiber (α := α) a sample = U)).card =
              (empiricalCountEventOnFinset
                (α := α) (ι := {i : ι // i ∉ U}) s k).card := by
          simpa [E] using
            empiricalCountEventOnFinset_fiber_card
              (α := α) (ι := ι) (s := s) (a := a) ha k U hUcard
        rw [hfiber]
        exact ih (ι := {i : ι // i ∉ U}) k hsum_compl
      calc
        (empiricalCountEventOnFinset
            (α := α) (ι := ι) (insert a s) k).card
            = E.card := by rfl
        _ =
            (fibers.biUnion
              (fun U : Finset ι =>
                E.filter
                  (fun sample : ι → α =>
                    labelFiber (α := α) a sample = U))).card := by
              exact congrArg Finset.card hcover
        _ =
            ∑ U ∈ fibers,
              (E.filter
                (fun sample : ι → α =>
                  labelFiber (α := α) a sample = U)).card := by
              rw [Finset.card_biUnion hdisj]
        _ =
            ∑ _U ∈ fibers, Nat.multinomial s k := by
              exact Finset.sum_congr rfl
                (fun U hU => hfiber_card U hU)
        _ = fibers.card * Nat.multinomial s k := by
              simp [Finset.sum_const]
        _ =
            (Fintype.card ι).choose (k a) *
              Nat.multinomial s k := by
              change
                (Finset.powersetCard (k a) (Finset.univ : Finset ι)).card *
                    Nat.multinomial s k =
                  (Fintype.card ι).choose (k a) * Nat.multinomial s k
              rw [Finset.card_powersetCard, Finset.card_univ]
        _ =
            (k a + ∑ x ∈ s, k x).choose (k a) *
              Nat.multinomial s k := by
              rw [htotal]
        _ = Nat.multinomial (insert a s) k := by
              rw [Nat.multinomial_insert ha]

/-- Cardinality of the empirical-count event is the multinomial coefficient. -/
theorem empiricalCountEventFinset_card_eq_multinomial
    (k : α → ℕ) {n : ℕ} (hk : ∑ a : α, k a = n) :
    (empiricalCountEventFinset (α := α) n k).card =
      Nat.multinomial (Finset.univ : Finset α) k := by
  classical
  have hcard :=
    empiricalCountEventOnFinset_card_eq_multinomial
      (α := α) (s := (Finset.univ : Finset α)) (ι := Fin n) k
      (by
        show ∑ a ∈ (Finset.univ : Finset α), k a = Fintype.card (Fin n)
        simpa [Fintype.card_fin] using hk)
  have hevent :
      empiricalCountEventOnFinset
          (α := α) (ι := Fin n) (Finset.univ : Finset α) k =
        empiricalCountEventFinset (α := α) n k := by
    ext sample
    simp [empiricalCountEventOnFinset, empiricalCountEventFinset]
  simpa [hevent] using hcard

/-- Empirical counts over all labels add up to the sample size. -/
theorem sum_empiricalCount_eq_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sample : ι → α) :
    ∑ a : α, empiricalCount sample a = Fintype.card ι := by
  classical
  have h :=
    finiteIidScoreSum_eq_sum_empiricalCount
      (α := α) (ι := ι) (score := fun _ : α => (1 : ℝ)) sample
  unfold finiteIidScoreSum at h
  simp only [mul_one] at h
  have hleft :
      (∑ i : ι, (1 : ℝ)) = (Fintype.card ι : ℝ) := by
    simp
  rw [hleft] at h
  exact_mod_cast h.symm

/--
If the requested counts do not sum to `n`, the empirical-count event is empty.
-/
theorem empiricalCountEventFinset_eq_empty_of_sum_ne
    {n : ℕ} {k : α → ℕ} (hk : ∑ a : α, k a ≠ n) :
    empiricalCountEventFinset (α := α) n k = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro sample hsample
  have hcounts :
      ∀ a : α, empiricalCount sample a = k a :=
    (mem_empiricalCountEventFinset (α := α)).mp hsample
  have hsum_counts := sum_empiricalCount_eq_card (α := α) sample
  have hsum_counts' :
      ∑ a : α, empiricalCount sample a = n := by
    calc
      ∑ a : α, empiricalCount sample a = Fintype.card (Fin n) := hsum_counts
      _ = n := Fintype.card_fin n
  have hsum_k : ∑ a : α, k a = n := by
    rw [← hsum_counts']
    refine Finset.sum_congr rfl ?_
    intro a _ha
    exact (hcounts a).symm
  exact hk hsum_k

/--
The canonical sample associated to a count vector whose entries sum to `n`.
-/
noncomputable def countVectorSample
    (k : α → ℕ) {n : ℕ} (hk : ∑ a : α, k a = n) :
    Fin n → α :=
  fun i => (countVectorSigmaEquiv k hk i).1

/-- The canonical count-vector sample has exactly the requested counts. -/
theorem empiricalCount_countVectorSample_eq
    (k : α → ℕ) {n : ℕ} (hk : ∑ a : α, k a = n) (a : α) :
    empiricalCount (countVectorSample (α := α) k hk) a = k a := by
  classical
  let bucket : α → Finset (Fin n) := countVectorBucket k hk
  have hsample :
      ∀ b : α, ∀ i : Fin n, i ∈ bucket b →
        countVectorSample (α := α) k hk i = b := by
    intro b i hi
    exact (mem_countVectorBucket k hk b i).mp hi
  calc
    empiricalCount (countVectorSample (α := α) k hk) a
        = (bucket a).card := by
          exact
            empiricalCount_eq_card_bucket_of_forall_mem_bucket
              (bucket := bucket)
              (hcover := countVectorBucket_cover k hk)
              (hdisj := countVectorBucket_disjoint k hk)
              (sample := countVectorSample (α := α) k hk)
              hsample a
    _ = k a := countVectorBucket_card k hk a

/--
If the requested counts sum to `n`, the empirical-count event is nonempty.
-/
theorem empiricalCountEventFinset_nonempty
    (k : α → ℕ) {n : ℕ} (hk : ∑ a : α, k a = n) :
    (empiricalCountEventFinset (α := α) n k).Nonempty := by
  classical
  refine ⟨countVectorSample (α := α) k hk, ?_⟩
  exact
    (mem_empiricalCountEventFinset (α := α)).mpr
      (empiricalCount_countVectorSample_eq (α := α) k hk)

/--
The `countPerms` multinomial coefficient of a multiset agrees with the
`Nat.multinomial` coefficient over the ambient finite type whenever the
multiset counts are the prescribed vector.
-/
theorem countPerms_eq_multinomial_univ_of_count
    (m : Multiset α) (k : α → ℕ)
    (hcount : ∀ a : α, m.count a = k a) :
    m.countPerms = Nat.multinomial (Finset.univ : Finset α) k := by
  classical
  rw [Multiset.countPerms]
  rw [← Finsupp.multinomial_of_support_subset (Finset.subset_univ _)]
  exact
    Nat.multinomial_congr
      (s := (Finset.univ : Finset α))
      (f := m.toFinsupp) (g := k)
      (by
        intro a _ha
        simpa [Multiset.toFinsupp_apply] using hcount a)

/--
The canonical count-vector sample has `countPerms` equal to the ambient
multinomial coefficient for the count vector.
-/
theorem countVectorSample_countPerms_eq_multinomial
    (k : α → ℕ) {n : ℕ} (hk : ∑ a : α, k a = n) :
    Multiset.countPerms
        ((List.ofFn (countVectorSample (α := α) k hk) : List α) : Multiset α) =
      Nat.multinomial (Finset.univ : Finset α) k := by
  classical
  refine
    countPerms_eq_multinomial_univ_of_count
      (m := (List.ofFn (countVectorSample (α := α) k hk) : Multiset α))
      k ?_
  intro a
  have hcounts :=
    empiricalCount_countVectorSample_eq (α := α) k hk a
  rw [Multiset.coe_count]
  exact (empiricalCount_eq_list_count_ofFn
    (countVectorSample (α := α) k hk) a).symm.trans hcounts

/--
Exact finite iid probability of a prescribed empirical-count event, expressed
as the empirical type cardinality times the common atom mass of that type.
-/
theorem pmfProduct_prob_empiricalCounts_eq_card_mul
    (μ : PMF α) {n : ℕ} (k : α → ℕ) :
    pmfProb (pmfProduct (Fin n) α μ)
        (fun sample : Fin n → α =>
          ∀ a : α, empiricalCount sample a = k a) =
      ((empiricalCountEventFinset (α := α) n k).card : ℝ) *
        ∏ a : α, (μ a).toReal ^ k a := by
  classical
  let countEvent : (Fin n → α) → Prop :=
    fun sample => ∀ a : α, empiricalCount sample a = k a
  let eventFinset : Finset (Fin n → α) :=
    empiricalCountEventFinset (α := α) n k
  have heventFinset :
      eventFinset =
        (Finset.univ : Finset (Fin n → α)).filter countEvent := by
    rfl
  have hmass :
      ∀ sample ∈ eventFinset,
        (pmfProduct (Fin n) α μ sample).toReal =
          ∏ a : α, (μ a).toReal ^ k a := by
    intro sample hsample
    have hcounts : ∀ a : α, empiricalCount sample a = k a := by
      simpa [eventFinset, countEvent] using hsample
    rw [pmfProduct_apply_toReal_eq_prod_empiricalCount]
    refine Finset.prod_congr rfl ?_
    intro a _ha
    rw [hcounts a]
  calc
    pmfProb (pmfProduct (Fin n) α μ) countEvent
        =
        ∑ sample : Fin n → α,
          (pmfProduct (Fin n) α μ sample).toReal *
            if countEvent sample then (1 : ℝ) else 0 := by
          rfl
    _ =
        ∑ sample : Fin n → α,
          if countEvent sample then
            (pmfProduct (Fin n) α μ sample).toReal else 0 := by
          refine Finset.sum_congr rfl ?_
          intro sample _hsample
          by_cases h : countEvent sample <;> simp [h]
    _ =
        ∑ sample ∈ eventFinset,
          (pmfProduct (Fin n) α μ sample).toReal := by
          rw [heventFinset, Finset.sum_filter]
    _ =
        ∑ _sample ∈ eventFinset,
          ∏ a : α, (μ a).toReal ^ k a := by
          refine Finset.sum_congr rfl ?_
          intro sample hsample
          exact hmass sample hsample
    _ =
        ((empiricalCountEventFinset (α := α) n k).card : ℝ) *
          ∏ a : α, (μ a).toReal ^ k a := by
          simp [eventFinset, Finset.sum_const, nsmul_eq_mul]

/--
Exact multinomial form, assuming the standard empirical-type cardinality
identity for the count vector.
-/
theorem pmfProduct_prob_empiricalCounts_eq_multinomial_of_card
    (μ : PMF α) {n : ℕ} (k : α → ℕ)
    (hcard :
      (empiricalCountEventFinset (α := α) n k).card =
        Nat.multinomial (Finset.univ : Finset α) k) :
    pmfProb (pmfProduct (Fin n) α μ)
        (fun sample : Fin n → α =>
          ∀ a : α, empiricalCount sample a = k a) =
      (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
        ∏ a : α, (μ a).toReal ^ k a := by
  rw [pmfProduct_prob_empiricalCounts_eq_card_mul (μ := μ) (k := k), hcard]

/-- Exact multinomial probability of a prescribed empirical-count event. -/
theorem pmfProduct_prob_empiricalCounts_eq_multinomial
    (μ : PMF α) {n : ℕ} (k : α → ℕ) (hk : ∑ a : α, k a = n) :
    pmfProb (pmfProduct (Fin n) α μ)
        (fun sample : Fin n → α =>
          ∀ a : α, empiricalCount sample a = k a) =
      (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
        ∏ a : α, (μ a).toReal ^ k a := by
  exact
    pmfProduct_prob_empiricalCounts_eq_multinomial_of_card
      (μ := μ) (k := k)
      (empiricalCountEventFinset_card_eq_multinomial (α := α) k hk)

/--
Lower-bound form with the multinomial coefficient, assuming only the matching
cardinality lower bound.
-/
theorem multinomial_mul_prod_le_pmfProduct_prob_empiricalCounts_of_card_le
    (μ : PMF α) {n : ℕ} (k : α → ℕ)
    (hcard :
      Nat.multinomial (Finset.univ : Finset α) k ≤
        (empiricalCountEventFinset (α := α) n k).card) :
    (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
        ∏ a : α, (μ a).toReal ^ k a ≤
      pmfProb (pmfProduct (Fin n) α μ)
        (fun sample : Fin n → α =>
          ∀ a : α, empiricalCount sample a = k a) := by
  classical
  rw [pmfProduct_prob_empiricalCounts_eq_card_mul (μ := μ) (k := k)]
  exact
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard)
      (Finset.prod_nonneg
        (fun a _ha => pow_nonneg ENNReal.toReal_nonneg (k a)))

/-- Lower-bound form of the exact empirical-count multinomial probability. -/
theorem multinomial_mul_prod_le_pmfProduct_prob_empiricalCounts
    (μ : PMF α) {n : ℕ} (k : α → ℕ) (hk : ∑ a : α, k a = n) :
    (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
        ∏ a : α, (μ a).toReal ^ k a ≤
      pmfProb (pmfProduct (Fin n) α μ)
        (fun sample : Fin n → α =>
          ∀ a : α, empiricalCount sample a = k a) := by
  rw [pmfProduct_prob_empiricalCounts_eq_multinomial (μ := μ) (k := k) hk]

private theorem nat_pow_mul_factorial_le_self_pow_mul_factorial
    (c n : ℕ) :
    c ^ n * Nat.factorial c ≤ c ^ c * Nat.factorial n := by
  rcases le_total c n with hcn | hnc
  · have hfact : Nat.factorial c * c ^ (n - c) ≤ Nat.factorial n :=
      Nat.factorial_mul_pow_sub_le_factorial hcn
    calc
      c ^ n * Nat.factorial c = c ^ (c + (n - c)) * Nat.factorial c := by
        rw [Nat.add_sub_of_le hcn]
      _ = c ^ c * (c ^ (n - c) * Nat.factorial c) := by
        rw [pow_add]
        ac_rfl
      _ ≤ c ^ c * Nat.factorial n := by
        exact Nat.mul_le_mul_left _ (by simpa [Nat.mul_comm] using hfact)
  · have hasc_eq :
        Nat.factorial n * (n + 1).ascFactorial (c - n) =
          Nat.factorial c := by
      have h := Nat.factorial_mul_ascFactorial n (c - n)
      simpa [Nat.add_sub_of_le hnc] using h
    have hasc_le : (n + 1).ascFactorial (c - n) ≤ c ^ (c - n) := by
      have h := Nat.ascFactorial_le_pow_add n (c - n)
      simpa [Nat.add_sub_of_le hnc] using h
    have hfact_le : Nat.factorial c ≤ Nat.factorial n * c ^ (c - n) := by
      rw [← hasc_eq]
      exact Nat.mul_le_mul_left _ hasc_le
    calc
      c ^ n * Nat.factorial c ≤
          c ^ n * (Nat.factorial n * c ^ (c - n)) := by
        exact Nat.mul_le_mul_left _ hfact_le
      _ = (c ^ n * c ^ (c - n)) * Nat.factorial n := by
        ac_rfl
      _ = c ^ c * Nat.factorial n := by
        rw [← pow_add, Nat.add_sub_of_le hnc]

omit [DecidableEq α] in
private theorem multinomial_mul_prod_pow_le_empirical_mode_nat
    (q k : α → ℕ) {Q : ℕ}
    (hqsum : ∑ a : α, q a = Q)
    (hksum : ∑ a : α, k a = Q) :
    Nat.multinomial (Finset.univ : Finset α) k *
        ∏ a : α, q a ^ k a ≤
      Nat.multinomial (Finset.univ : Finset α) q *
        ∏ a : α, q a ^ q a := by
  classical
  let K : ℕ := ∏ a : α, Nat.factorial (k a)
  let R : ℕ := ∏ a : α, Nat.factorial (q a)
  let A : ℕ := ∏ a : α, q a ^ k a
  let B : ℕ := ∏ a : α, q a ^ q a
  have hcoord :
      ∀ a : α,
        q a ^ k a * Nat.factorial (q a) ≤
          q a ^ q a * Nat.factorial (k a) := by
    intro a
    exact nat_pow_mul_factorial_le_self_pow_mul_factorial (q a) (k a)
  have hprod :
      A * R ≤ B * K := by
    dsimp [A, B, K, R]
    calc
      (∏ a : α, q a ^ k a) * (∏ a : α, Nat.factorial (q a))
          = ∏ a : α, q a ^ k a * Nat.factorial (q a) := by
            rw [Finset.prod_mul_distrib]
      _ ≤ ∏ a : α, q a ^ q a * Nat.factorial (k a) := by
            exact Finset.prod_le_prod
              (fun _a _ha => Nat.zero_le _)
              (fun a _ha => hcoord a)
      _ = (∏ a : α, q a ^ q a) *
            (∏ a : α, Nat.factorial (k a)) := by
            rw [Finset.prod_mul_distrib]
  have hKspec :
      K * Nat.multinomial (Finset.univ : Finset α) k = Nat.factorial Q := by
    dsimp [K]
    simpa [hksum] using
      (Nat.multinomial_spec (Finset.univ : Finset α) k)
  have hRspec :
      R * Nat.multinomial (Finset.univ : Finset α) q = Nat.factorial Q := by
    dsimp [R]
    simpa [hqsum] using
      (Nat.multinomial_spec (Finset.univ : Finset α) q)
  have hKRpos : 0 < K * R := by
    dsimp [K, R]
    exact Nat.mul_pos
      (Finset.prod_pos (fun a _ha => Nat.factorial_pos (k a)))
      (Finset.prod_pos (fun a _ha => Nat.factorial_pos (q a)))
  exact Nat.le_of_mul_le_mul_right
    (calc
      (Nat.multinomial (Finset.univ : Finset α) k * A) * (K * R)
          = (K * Nat.multinomial (Finset.univ : Finset α) k) * (A * R) := by
            ac_rfl
      _ = Nat.factorial Q * (A * R) := by
            rw [hKspec]
      _ ≤ Nat.factorial Q * (B * K) := by
            exact Nat.mul_le_mul_left _ hprod
      _ = (R * Nat.multinomial (Finset.univ : Finset α) q) * (B * K) := by
            rw [hRspec]
      _ = (Nat.multinomial (Finset.univ : Finset α) q * B) * (K * R) := by
            ac_rfl)
    hKRpos

/--
The empirical count vector is a mode of its own multinomial law.

In raw integer weights, if both `q` and `k` have total mass `Q`, then the
multinomial term with atom weights `q a` is maximized at `k = q`.
-/
theorem multinomial_mul_prod_pow_le_empirical_mode
    (q k : α → ℕ) {Q : ℕ}
    (hqsum : ∑ a : α, q a = Q)
    (hksum : ∑ a : α, k a = Q) :
    (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
        ∏ a : α, (q a : ℝ) ^ k a ≤
      (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
        ∏ a : α, (q a : ℝ) ^ q a := by
  exact_mod_cast
    multinomial_mul_prod_pow_le_empirical_mode_nat
      (α := α) q k hqsum hksum

/--
The number of finite count vectors of total mass `Q` is at most
`(Q + 1) ^ card α`.
-/
theorem piAntidiag_univ_card_le (Q : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset α) Q).card ≤
      Q.succ ^ Fintype.card α := by
  classical
  let encode :
      {k : α → ℕ // k ∈ Finset.piAntidiag (Finset.univ : Finset α) Q} →
        α → Fin Q.succ :=
    fun k a =>
      ⟨k.1 a, by
        have hsum : ∑ b : α, k.1 b = Q := by
          simpa using (Finset.mem_piAntidiag.mp k.2).1
        have hle : k.1 a ≤ ∑ b : α, k.1 b :=
          Finset.single_le_sum
            (fun b _hb => Nat.zero_le (k.1 b))
            (Finset.mem_univ a)
        exact Nat.lt_succ_of_le (by simpa [hsum] using hle)⟩
  have hencode_inj : Function.Injective encode := by
    intro k l hkl
    apply Subtype.ext
    funext a
    exact congrArg Fin.val (congrFun hkl a)
  have hcard :=
    Fintype.card_le_of_injective encode hencode_inj
  simpa [Fintype.card_coe, Fintype.card_fun] using hcard

/--
Finite method-of-types lower bound for an empirical multinomial mode.

For any positive total count `Q`, the count vector `q` has at least inverse
polynomial mass under its own empirical law `a ↦ q a / Q`.
-/
theorem multinomial_empirical_mode_mass_ge_inv_countVectors
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ)
    (hqsum : ∑ a : α, q a = Q) :
    (1 / (((Q.succ : ℕ) : ℝ) ^ Fintype.card α)) ≤
      (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
        ∏ a : α, (((q a : ℝ) / Q) ^ q a) := by
  classical
  let rawMode : ℝ :=
    (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
      ∏ a : α, (q a : ℝ) ^ q a
  let countBound : ℝ := ((Q.succ : ℕ) : ℝ) ^ Fintype.card α
  let denom : ℝ := (Q : ℝ) ^ Q
  have hQreal_pos : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact pow_pos hQreal_pos Q
  have hcountBound_pos : 0 < countBound := by
    dsimp [countBound]
    exact pow_pos (by exact_mod_cast Nat.succ_pos Q) _
  have hrawMode_nonneg : 0 ≤ rawMode := by
    dsimp [rawMode]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le _)
      (Finset.prod_nonneg
        (fun a _ha => pow_nonneg (by exact_mod_cast Nat.zero_le (q a)) _))
  have hsum_q_real : ∑ a : α, (q a : ℝ) = (Q : ℝ) := by
    exact_mod_cast hqsum
  have hmultinomial_sum :
      denom =
        ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) Q,
          (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
            ∏ a : α, (q a : ℝ) ^ k a := by
    dsimp [denom]
    calc
      (Q : ℝ) ^ Q =
          (∑ a ∈ (Finset.univ : Finset α), (q a : ℝ)) ^ Q := by
            rw [show ∑ a ∈ (Finset.univ : Finset α), (q a : ℝ) =
                (Q : ℝ) by simpa using hsum_q_real]
      _ =
          ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) Q,
            Nat.multinomial (Finset.univ : Finset α) k *
              ∏ a ∈ (Finset.univ : Finset α), (q a : ℝ) ^ k a := by
            rw [Finset.sum_pow_eq_sum_piAntidiag]
      _ =
          ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) Q,
            (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
              ∏ a : α, (q a : ℝ) ^ k a := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            simp
  have hterm_le :
      ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) Q,
        (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
            ∏ a : α, (q a : ℝ) ^ k a ≤ rawMode := by
    intro k hk
    have hksum : ∑ a : α, k a = Q := by
      simpa using (Finset.mem_piAntidiag.mp hk).1
    simpa [rawMode] using
      multinomial_mul_prod_pow_le_empirical_mode
        (α := α) q k hqsum hksum
  have hsum_le :
      (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) Q,
          (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
            ∏ a : α, (q a : ℝ) ^ k a) ≤
        ((Finset.piAntidiag (Finset.univ : Finset α) Q).card : ℝ) *
          rawMode := by
    have h :=
      Finset.sum_le_card_nsmul
        (Finset.piAntidiag (Finset.univ : Finset α) Q)
        (fun k =>
          (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
            ∏ a : α, (q a : ℝ) ^ k a)
        rawMode hterm_le
    simpa [nsmul_eq_mul] using h
  have hcard_real :
      ((Finset.piAntidiag (Finset.univ : Finset α) Q).card : ℝ) ≤
        countBound := by
    dsimp [countBound]
    exact_mod_cast (piAntidiag_univ_card_le (α := α) Q)
  have hdenom_le_bound_raw : denom ≤ countBound * rawMode := by
    calc
      denom =
          ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) Q,
            (Nat.multinomial (Finset.univ : Finset α) k : ℝ) *
              ∏ a : α, (q a : ℝ) ^ k a := hmultinomial_sum
      _ ≤
          ((Finset.piAntidiag (Finset.univ : Finset α) Q).card : ℝ) *
            rawMode := hsum_le
      _ ≤ countBound * rawMode :=
            mul_le_mul_of_nonneg_right hcard_real hrawMode_nonneg
  have hraw_lower : denom / countBound ≤ rawMode := by
    rw [div_le_iff₀ hcountBound_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdenom_le_bound_raw
  have hmode_eq_raw_div :
      (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
          ∏ a : α, (((q a : ℝ) / Q) ^ q a) =
        rawMode / denom := by
    have hprod_div :
        ∏ a : α, (((q a : ℝ) / Q) ^ q a) =
          (∏ a : α, (q a : ℝ) ^ q a) / denom := by
      dsimp [denom]
      calc
        ∏ a : α, (((q a : ℝ) / Q) ^ q a)
            =
            ∏ a : α, ((q a : ℝ) ^ q a / (Q : ℝ) ^ q a) := by
              refine Finset.prod_congr rfl ?_
              intro a _ha
              rw [div_pow]
        _ =
            (∏ a : α, (q a : ℝ) ^ q a) /
              ∏ a : α, (Q : ℝ) ^ q a := by
              rw [Finset.prod_div_distrib]
        _ =
            (∏ a : α, (q a : ℝ) ^ q a) / (Q : ℝ) ^ Q := by
              rw [Finset.prod_pow_eq_pow_sum]
              rw [hqsum]
    rw [hprod_div]
    dsimp [rawMode]
    ring
  have htarget_raw : 1 / countBound ≤ rawMode / denom := by
    rw [le_div_iff₀ hdenom_pos]
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hraw_lower
  simpa [countBound, hmode_eq_raw_div]
    using htarget_raw

/--
A strict negative mean simplex point admits a nearby integer empirical type
whose total score is nonpositive.

This denominator-controlled variant is the rate-sensitive form used by
method-of-types lower bounds: the caller chooses a large `Q`, and the simplex
rounding theorem supplies an empirical type with denominator exactly `Q`.
-/
theorem exists_countVector_tail_close_to_simplex_of_neg_mean_of_large_denominator
    [Nonempty α]
    (ν : α → ℝ) (score : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    {Q : ℕ} (hQpos : 0 < Q)
    {ε : ℝ} (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < ε)
    (hmargin :
      ε * (∑ a : α, |score a|) ≤
        -(∑ a : α, ν a * score a)) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α, |((q a : ℝ) / Q) - ν a| < ε) ∧
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
  classical
  obtain ⟨q, hqsum, hqclose⟩ :=
    AppliedModelingLib.SimplexRounding.exists_countVector_close_to_simplex_of_large_denominator
      ν hν_nonneg hν_sum hQpos hQ_large
  have hQpos_real : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  let freq : α → ℝ := fun a => (q a : ℝ) / (Q : ℝ)
  have hdiff_eq :
      (∑ a : α, freq a * score a) -
          (∑ a : α, ν a * score a) =
        ∑ a : α, (freq a - ν a) * score a := by
    calc
      (∑ a : α, freq a * score a) -
          (∑ a : α, ν a * score a)
          =
          ∑ a : α, (freq a * score a - ν a * score a) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ a : α, (freq a - ν a) * score a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
  have hdiff_le :
      ∑ a : α, (freq a - ν a) * score a ≤
        ε * (∑ a : α, |score a|) := by
    calc
      ∑ a : α, (freq a - ν a) * score a
          ≤ ∑ a : α, ε * |score a| := by
            refine Finset.sum_le_sum ?_
            intro a _
            calc
              (freq a - ν a) * score a
                  ≤ |(freq a - ν a) * score a| := le_abs_self _
              _ = |freq a - ν a| * |score a| := by rw [abs_mul]
              _ ≤ ε * |score a| :=
                    mul_le_mul_of_nonneg_right
                      (le_of_lt (by simpa [freq] using hqclose a))
                      (abs_nonneg _)
      _ = ε * (∑ a : α, |score a|) := by
            rw [Finset.mul_sum]
  have hfreq_score_nonpos :
      ∑ a : α, freq a * score a ≤ 0 := by
    have hsum_le :
        (∑ a : α, freq a * score a) -
            (∑ a : α, ν a * score a) ≤
          ε * (∑ a : α, |score a|) := by
      simpa [hdiff_eq] using hdiff_le
    linarith
  have htail_div :
      (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ) =
        ∑ a : α, freq a * score a := by
    calc
      (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ)
          = ∑ a : α, ((q a : ℝ) * score a) / (Q : ℝ) := by
            rw [Finset.sum_div]
      _ = ∑ a : α, freq a * score a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            dsimp [freq]
            ring
  have htail_nonpos :
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
    have hdiv_nonpos :
        (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ) ≤ 0 := by
      simpa [htail_div] using hfreq_score_nonpos
    have hmul :
        ∑ a : α, (q a : ℝ) * score a ≤ 0 * (Q : ℝ) :=
      (div_le_iff₀ hQpos_real).mp (by simpa using hdiv_nonpos)
    have hzero : (0 : ℝ) * (Q : ℝ) = 0 := by ring
    rwa [hzero] at hmul
  exact ⟨q, hqsum, hqclose, htail_nonpos⟩

/--
Anchored, support-preserving version of
`exists_countVector_tail_close_to_simplex_of_neg_mean_of_large_denominator`.

The returned support fact says any nonzero rounded count is either the chosen
anchor or lies on a strictly positive coordinate of the target simplex point.
-/
theorem exists_countVector_tail_close_to_simplex_of_neg_mean_of_large_denominator_with_anchor
    [Nonempty α]
    (ν : α → ℝ) (score : α → ℝ) (a₀ : α)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    {Q : ℕ} (hQpos : 0 < Q)
    {ε : ℝ} (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < ε)
    (hmargin :
      ε * (∑ a : α, |score a|) ≤
        -(∑ a : α, ν a * score a)) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α, |((q a : ℝ) / Q) - ν a| < ε) ∧
      (∑ a : α, (q a : ℝ) * score a ≤ 0) ∧
      ∀ a : α, q a ≠ 0 → a = a₀ ∨ 0 < ν a := by
  classical
  obtain ⟨q, hqsum, hqclose, hq_support⟩ :=
    AppliedModelingLib.SimplexRounding.exists_countVector_close_to_simplex_of_large_denominator_with_anchor
      ν a₀ hν_nonneg hν_sum hQpos hQ_large
  have hQpos_real : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  let freq : α → ℝ := fun a => (q a : ℝ) / (Q : ℝ)
  have hdiff_eq :
      (∑ a : α, freq a * score a) -
          (∑ a : α, ν a * score a) =
        ∑ a : α, (freq a - ν a) * score a := by
    calc
      (∑ a : α, freq a * score a) -
          (∑ a : α, ν a * score a)
          =
          ∑ a : α, (freq a * score a - ν a * score a) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ a : α, (freq a - ν a) * score a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
  have hdiff_le :
      ∑ a : α, (freq a - ν a) * score a ≤
        ε * (∑ a : α, |score a|) := by
    calc
      ∑ a : α, (freq a - ν a) * score a
          ≤ ∑ a : α, ε * |score a| := by
            refine Finset.sum_le_sum ?_
            intro a _
            calc
              (freq a - ν a) * score a
                  ≤ |(freq a - ν a) * score a| := le_abs_self _
              _ = |freq a - ν a| * |score a| := by rw [abs_mul]
              _ ≤ ε * |score a| :=
                    mul_le_mul_of_nonneg_right
                      (le_of_lt (by simpa [freq] using hqclose a))
                      (abs_nonneg _)
      _ = ε * (∑ a : α, |score a|) := by
            rw [Finset.mul_sum]
  have hfreq_score_nonpos :
      ∑ a : α, freq a * score a ≤ 0 := by
    have hsum_le :
        (∑ a : α, freq a * score a) -
            (∑ a : α, ν a * score a) ≤
          ε * (∑ a : α, |score a|) := by
      simpa [hdiff_eq] using hdiff_le
    linarith
  have htail_div :
      (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ) =
        ∑ a : α, freq a * score a := by
    calc
      (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ)
          = ∑ a : α, ((q a : ℝ) * score a) / (Q : ℝ) := by
            rw [Finset.sum_div]
      _ = ∑ a : α, freq a * score a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            dsimp [freq]
            ring
  have htail_nonpos :
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
    have hdiv_nonpos :
        (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ) ≤ 0 := by
      simpa [htail_div] using hfreq_score_nonpos
    have hmul :
        ∑ a : α, (q a : ℝ) * score a ≤ 0 * (Q : ℝ) :=
      (div_le_iff₀ hQpos_real).mp (by simpa using hdiv_nonpos)
    have hzero : (0 : ℝ) * (Q : ℝ) = 0 := by ring
    rwa [hzero] at hmul
  exact ⟨q, hqsum, hqclose, htail_nonpos, hq_support⟩

/--
A strict negative mean simplex point admits a nearby integer empirical type
whose total score is nonpositive.

This is the finite rounding side of the method-of-types lower bound.  The
margin assumption says the coordinatewise approximation error is small enough
relative to the finite score scale.
-/
theorem exists_countVector_tail_close_to_simplex_of_neg_mean
    [Nonempty α]
    (ν : α → ℝ) (score : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    {ε : ℝ} (hε : 0 < ε)
    (hmargin :
      ε * (∑ a : α, |score a|) ≤
        -(∑ a : α, ν a * score a)) :
    ∃ (Q : ℕ) (q : α → ℕ),
      0 < Q ∧
      (∑ a : α, q a = Q) ∧
      (∀ a : α, |((q a : ℝ) / Q) - ν a| < ε) ∧
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
  classical
  obtain ⟨Q, q, hQpos, hqsum, hqclose⟩ :=
    AppliedModelingLib.SimplexRounding.exists_countVector_close_to_simplex
      ν hν_nonneg hν_sum hε
  have hQpos_real : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  let freq : α → ℝ := fun a => (q a : ℝ) / (Q : ℝ)
  have hdiff_eq :
      (∑ a : α, freq a * score a) -
          (∑ a : α, ν a * score a) =
        ∑ a : α, (freq a - ν a) * score a := by
    calc
      (∑ a : α, freq a * score a) -
          (∑ a : α, ν a * score a)
          =
          ∑ a : α, (freq a * score a - ν a * score a) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ a : α, (freq a - ν a) * score a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
  have hdiff_le :
      ∑ a : α, (freq a - ν a) * score a ≤
        ε * (∑ a : α, |score a|) := by
    calc
      ∑ a : α, (freq a - ν a) * score a
          ≤ ∑ a : α, ε * |score a| := by
            refine Finset.sum_le_sum ?_
            intro a _
            calc
              (freq a - ν a) * score a
                  ≤ |(freq a - ν a) * score a| := le_abs_self _
              _ = |freq a - ν a| * |score a| := by rw [abs_mul]
              _ ≤ ε * |score a| :=
                    mul_le_mul_of_nonneg_right
                      (le_of_lt (by simpa [freq] using hqclose a))
                      (abs_nonneg _)
      _ = ε * (∑ a : α, |score a|) := by
            rw [Finset.mul_sum]
  have hfreq_score_nonpos :
      ∑ a : α, freq a * score a ≤ 0 := by
    have hsum_le :
        (∑ a : α, freq a * score a) -
            (∑ a : α, ν a * score a) ≤
          ε * (∑ a : α, |score a|) := by
      simpa [hdiff_eq] using hdiff_le
    linarith
  have htail_div :
      (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ) =
        ∑ a : α, freq a * score a := by
    calc
      (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ)
          = ∑ a : α, ((q a : ℝ) * score a) / (Q : ℝ) := by
            rw [Finset.sum_div]
      _ = ∑ a : α, freq a * score a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            dsimp [freq]
            ring
  have htail_nonpos :
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
    have hdiv_nonpos :
        (∑ a : α, (q a : ℝ) * score a) / (Q : ℝ) ≤ 0 := by
      simpa [htail_div] using hfreq_score_nonpos
    have hmul :
        ∑ a : α, (q a : ℝ) * score a ≤ 0 * (Q : ℝ) :=
      (div_le_iff₀ hQpos_real).mp (by simpa using hdiv_nonpos)
    have hzero : (0 : ℝ) * (Q : ℝ) = 0 := by ring
    rwa [hzero] at hmul
  exact ⟨Q, q, hQpos, hqsum, hqclose, htail_nonpos⟩

/--
Tail-safe count-vector approximation near a zero-mean simplex point.

The construction perturbs `ν` by weight `δ` toward a negative-score atom and
then applies `exists_countVector_tail_close_to_simplex_of_neg_mean` to the
perturbed simplex point.  The explicit `η`/`δ` assumptions keep this lemma
usable without hiding rate-sensitive choices.
-/
theorem exists_countVector_tail_close_to_zero_mean_simplex_via_neg_atom
    [Nonempty α]
    (ν : α → ℝ) (score : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    (hν_mean : ∑ a : α, ν a * score a = 0)
    {aNeg : α} (hscoreNeg : score aNeg < 0)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hmargin :
      η * (∑ a : α, |score a|) ≤ δ * (-(score aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ (Q : ℕ) (q : α → ℕ),
      0 < Q ∧
      (∑ a : α, q a = Q) ∧
      (∀ a : α, |((q a : ℝ) / Q) - ν a| < ε) ∧
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
  classical
  let νδ : α → ℝ := fun a =>
    (1 - δ) * ν a + if a = aNeg then δ else 0
  have hν_le_one : ∀ a : α, ν a ≤ 1 := by
    intro a
    calc
      ν a ≤ ∑ b : α, ν b := by
        exact
          Finset.single_le_sum
            (fun b _hb => hν_nonneg b)
            (Finset.mem_univ a)
      _ = 1 := hν_sum
  have hνδ_nonneg : ∀ a : α, 0 ≤ νδ a := by
    intro a
    dsimp [νδ]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hδ_le_one) (hν_nonneg a))
      (by by_cases h : a = aNeg <;> simp [h, hδ_nonneg])
  have hνδ_sum : ∑ a : α, νδ a = 1 := by
    calc
      ∑ a : α, νδ a
          =
          ∑ a : α, ((1 - δ) * ν a) +
            ∑ a : α, (if a = aNeg then δ else 0) := by
            dsimp [νδ]
            rw [Finset.sum_add_distrib]
      _ = (1 - δ) * (∑ a : α, ν a) +
            ∑ a : α, (if a = aNeg then δ else 0) := by
            rw [Finset.mul_sum]
      _ = (1 - δ) * 1 + δ := by
            rw [hν_sum]
            congr 1
            exact Fintype.sum_ite_eq' aNeg (fun _a : α => δ)
      _ = 1 := by ring
  have hνδ_mean :
      ∑ a : α, νδ a * score a = δ * score aNeg := by
    calc
      ∑ a : α, νδ a * score a
          =
          ∑ a : α,
            (((1 - δ) * ν a) * score a +
              (if a = aNeg then δ else 0) * score a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            dsimp [νδ]
            ring
      _ =
          ∑ a : α, ((1 - δ) * (ν a * score a)) +
            ∑ a : α, ((if a = aNeg then δ else 0) * score a) := by
            rw [Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
      _ =
          (1 - δ) * (∑ a : α, ν a * score a) +
            ∑ a : α, ((if a = aNeg then δ else 0) * score a) := by
            rw [Finset.mul_sum]
      _ = (1 - δ) * 0 + δ * score aNeg := by
            rw [hν_mean]
            congr 1
            calc
              ∑ a : α, ((if a = aNeg then δ else 0) * score a)
                  =
                  ∑ a : α, (if a = aNeg then δ * score a else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    by_cases h : a = aNeg <;> simp [h]
              _ = δ * score aNeg :=
                    Fintype.sum_ite_eq' aNeg (fun a : α => δ * score a)
      _ = δ * score aNeg := by ring
  have hνδ_margin :
      η * (∑ a : α, |score a|) ≤
        -(∑ a : α, νδ a * score a) := by
    rw [hνδ_mean]
    linarith
  obtain ⟨Q, q, hQpos, hqsum, hqclose_νδ, htail⟩ :=
    exists_countVector_tail_close_to_simplex_of_neg_mean
      νδ score hνδ_nonneg hνδ_sum hη_pos hνδ_margin
  refine ⟨Q, q, hQpos, hqsum, ?_, htail⟩
  intro a
  have hνδ_close : |νδ a - ν a| ≤ δ := by
    dsimp [νδ]
    by_cases h : a = aNeg
    · subst a
      have hbetween : |1 - ν aNeg| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (hν_le_one aNeg))]
        linarith [hν_nonneg aNeg]
      have hrewrite :
          (1 - δ) * ν aNeg + δ - ν aNeg =
            δ * (1 - ν aNeg) := by ring
      rw [if_pos rfl, hrewrite, abs_mul]
      calc
        |δ| * |1 - ν aNeg| ≤ δ * 1 := by
          rw [abs_of_nonneg hδ_nonneg]
          exact mul_le_mul_of_nonneg_left hbetween hδ_nonneg
        _ = δ := by ring
    · have hbetween : |0 - ν a| ≤ 1 := by
        simp [abs_of_nonneg (hν_nonneg a)]
        exact hν_le_one a
      have hrewrite :
          (1 - δ) * ν a + 0 - ν a =
            δ * (0 - ν a) := by ring
      rw [if_neg h, hrewrite, abs_mul]
      calc
        |δ| * |0 - ν a| ≤ δ * 1 := by
          rw [abs_of_nonneg hδ_nonneg]
          exact mul_le_mul_of_nonneg_left hbetween hδ_nonneg
        _ = δ := by ring
  calc
    |((q a : ℝ) / Q) - ν a|
        ≤ |((q a : ℝ) / Q) - νδ a| + |νδ a - ν a| := by
          have hsplit :
              ((q a : ℝ) / Q) - ν a =
                (((q a : ℝ) / Q) - νδ a) + (νδ a - ν a) := by
            ring
          rw [hsplit]
          exact abs_add_le _ _
    _ < η + δ := add_lt_add_of_lt_of_le (hqclose_νδ a) hνδ_close
    _ < ε := hclose_total

/--
Denominator-controlled tail-safe count-vector approximation near a zero-mean
simplex point.

This is the rate-sensitive version of
`exists_countVector_tail_close_to_zero_mean_simplex_via_neg_atom`: callers pick
`Q` large enough for both approximation and method-of-types polynomial-loss
absorption.
-/
theorem exists_countVector_tail_close_to_zero_mean_simplex_via_neg_atom_of_large_denominator
    [Nonempty α]
    (ν : α → ℝ) (score : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    (hν_mean : ∑ a : α, ν a * score a = 0)
    {aNeg : α} (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < η)
    (hmargin :
      η * (∑ a : α, |score a|) ≤ δ * (-(score aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α, |((q a : ℝ) / Q) - ν a| < ε) ∧
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
  classical
  let νδ : α → ℝ := fun a =>
    (1 - δ) * ν a + if a = aNeg then δ else 0
  have hν_le_one : ∀ a : α, ν a ≤ 1 := by
    intro a
    calc
      ν a ≤ ∑ b : α, ν b := by
        exact
          Finset.single_le_sum
            (fun b _hb => hν_nonneg b)
            (Finset.mem_univ a)
      _ = 1 := hν_sum
  have hνδ_nonneg : ∀ a : α, 0 ≤ νδ a := by
    intro a
    dsimp [νδ]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hδ_le_one) (hν_nonneg a))
      (by by_cases h : a = aNeg <;> simp [h, hδ_nonneg])
  have hνδ_sum : ∑ a : α, νδ a = 1 := by
    calc
      ∑ a : α, νδ a
          =
          ∑ a : α, ((1 - δ) * ν a) +
            ∑ a : α, (if a = aNeg then δ else 0) := by
            dsimp [νδ]
            rw [Finset.sum_add_distrib]
      _ = (1 - δ) * (∑ a : α, ν a) +
            ∑ a : α, (if a = aNeg then δ else 0) := by
            rw [Finset.mul_sum]
      _ = (1 - δ) * 1 + δ := by
            rw [hν_sum]
            congr 1
            exact Fintype.sum_ite_eq' aNeg (fun _a : α => δ)
      _ = 1 := by ring
  have hνδ_mean :
      ∑ a : α, νδ a * score a = δ * score aNeg := by
    calc
      ∑ a : α, νδ a * score a
          =
          ∑ a : α,
            (((1 - δ) * ν a) * score a +
              (if a = aNeg then δ else 0) * score a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            dsimp [νδ]
            ring
      _ =
          ∑ a : α, ((1 - δ) * (ν a * score a)) +
            ∑ a : α, ((if a = aNeg then δ else 0) * score a) := by
            rw [Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
      _ =
          (1 - δ) * (∑ a : α, ν a * score a) +
            ∑ a : α, ((if a = aNeg then δ else 0) * score a) := by
            rw [Finset.mul_sum]
      _ = (1 - δ) * 0 + δ * score aNeg := by
            rw [hν_mean]
            congr 1
            calc
              ∑ a : α, ((if a = aNeg then δ else 0) * score a)
                  =
                  ∑ a : α, (if a = aNeg then δ * score a else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    by_cases h : a = aNeg <;> simp [h]
              _ = δ * score aNeg :=
                    Fintype.sum_ite_eq' aNeg (fun a : α => δ * score a)
      _ = δ * score aNeg := by ring
  have hνδ_margin :
      η * (∑ a : α, |score a|) ≤
        -(∑ a : α, νδ a * score a) := by
    rw [hνδ_mean]
    linarith
  obtain ⟨q, hqsum, hqclose_νδ, htail⟩ :=
    exists_countVector_tail_close_to_simplex_of_neg_mean_of_large_denominator
      νδ score hνδ_nonneg hνδ_sum hQpos hQ_large hνδ_margin
  refine ⟨q, hqsum, ?_, htail⟩
  intro a
  have hνδ_close : |νδ a - ν a| ≤ δ := by
    dsimp [νδ]
    by_cases h : a = aNeg
    · subst a
      have hbetween : |1 - ν aNeg| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (hν_le_one aNeg))]
        linarith [hν_nonneg aNeg]
      have hrewrite :
          (1 - δ) * ν aNeg + δ - ν aNeg =
            δ * (1 - ν aNeg) := by ring
      rw [if_pos rfl, hrewrite, abs_mul]
      calc
        |δ| * |1 - ν aNeg| ≤ δ * 1 := by
          rw [abs_of_nonneg hδ_nonneg]
          exact mul_le_mul_of_nonneg_left hbetween hδ_nonneg
        _ = δ := by ring
    · have hbetween : |0 - ν a| ≤ 1 := by
        simp [abs_of_nonneg (hν_nonneg a)]
        exact hν_le_one a
      have hrewrite :
          (1 - δ) * ν a + 0 - ν a =
            δ * (0 - ν a) := by ring
      rw [if_neg h, hrewrite, abs_mul]
      calc
        |δ| * |0 - ν a| ≤ δ * 1 := by
          rw [abs_of_nonneg hδ_nonneg]
          exact mul_le_mul_of_nonneg_left hbetween hδ_nonneg
        _ = δ := by ring
  calc
    |((q a : ℝ) / Q) - ν a|
        ≤ |((q a : ℝ) / Q) - νδ a| + |νδ a - ν a| := by
          have hsplit :
              ((q a : ℝ) / Q) - ν a =
                (((q a : ℝ) / Q) - νδ a) + (νδ a - ν a) := by
            ring
          rw [hsplit]
          exact abs_add_le _ _
    _ < η + δ := add_lt_add_of_lt_of_le (hqclose_νδ a) hνδ_close
    _ < ε := hclose_total

/--
Support-preserving denominator-controlled tail-safe approximation near a
zero-mean simplex point.

The support conclusion is stated relative to the original zero-mean point
`ν`, even though the proof rounds the perturbed point
`(1 - δ)ν + δ * pointMass(aNeg)`.
-/
theorem exists_countVector_tail_close_to_zero_mean_simplex_via_neg_atom_of_large_denominator_with_support
    [Nonempty α]
    (ν : α → ℝ) (score : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    (hν_mean : ∑ a : α, ν a * score a = 0)
    {aNeg : α} (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < η)
    (hmargin :
      η * (∑ a : α, |score a|) ≤ δ * (-(score aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α, |((q a : ℝ) / Q) - ν a| < ε) ∧
      (∑ a : α, (q a : ℝ) * score a ≤ 0) ∧
      ∀ a : α, q a ≠ 0 → a = aNeg ∨ 0 < ν a := by
  classical
  let νδ : α → ℝ := fun a =>
    (1 - δ) * ν a + if a = aNeg then δ else 0
  have hν_le_one : ∀ a : α, ν a ≤ 1 := by
    intro a
    calc
      ν a ≤ ∑ b : α, ν b := by
        exact
          Finset.single_le_sum
            (fun b _hb => hν_nonneg b)
            (Finset.mem_univ a)
      _ = 1 := hν_sum
  have hνδ_nonneg : ∀ a : α, 0 ≤ νδ a := by
    intro a
    dsimp [νδ]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hδ_le_one) (hν_nonneg a))
      (by by_cases h : a = aNeg <;> simp [h, hδ_nonneg])
  have hνδ_sum : ∑ a : α, νδ a = 1 := by
    calc
      ∑ a : α, νδ a
          =
          ∑ a : α, ((1 - δ) * ν a) +
            ∑ a : α, (if a = aNeg then δ else 0) := by
            dsimp [νδ]
            rw [Finset.sum_add_distrib]
      _ = (1 - δ) * (∑ a : α, ν a) +
            ∑ a : α, (if a = aNeg then δ else 0) := by
            rw [Finset.mul_sum]
      _ = (1 - δ) * 1 + δ := by
            rw [hν_sum]
            congr 1
            exact Fintype.sum_ite_eq' aNeg (fun _a : α => δ)
      _ = 1 := by ring
  have hνδ_mean :
      ∑ a : α, νδ a * score a = δ * score aNeg := by
    calc
      ∑ a : α, νδ a * score a
          =
          ∑ a : α,
            (((1 - δ) * ν a) * score a +
              (if a = aNeg then δ else 0) * score a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            dsimp [νδ]
            ring
      _ =
          ∑ a : α, ((1 - δ) * (ν a * score a)) +
            ∑ a : α, ((if a = aNeg then δ else 0) * score a) := by
            rw [Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
      _ =
          (1 - δ) * (∑ a : α, ν a * score a) +
            ∑ a : α, ((if a = aNeg then δ else 0) * score a) := by
            rw [Finset.mul_sum]
      _ = (1 - δ) * 0 + δ * score aNeg := by
            rw [hν_mean]
            congr 1
            calc
              ∑ a : α, ((if a = aNeg then δ else 0) * score a)
                  =
                  ∑ a : α, (if a = aNeg then δ * score a else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    by_cases h : a = aNeg <;> simp [h]
              _ = δ * score aNeg :=
                    Fintype.sum_ite_eq' aNeg (fun a : α => δ * score a)
      _ = δ * score aNeg := by ring
  have hνδ_margin :
      η * (∑ a : α, |score a|) ≤
        -(∑ a : α, νδ a * score a) := by
    rw [hνδ_mean]
    linarith
  obtain ⟨q, hqsum, hqclose_νδ, htail, hq_support_νδ⟩ :=
    exists_countVector_tail_close_to_simplex_of_neg_mean_of_large_denominator_with_anchor
      νδ score aNeg hνδ_nonneg hνδ_sum hQpos hQ_large hνδ_margin
  refine ⟨q, hqsum, ?_, htail, ?_⟩
  · intro a
    have hνδ_close : |νδ a - ν a| ≤ δ := by
      dsimp [νδ]
      by_cases h : a = aNeg
      · subst a
        have hbetween : |1 - ν aNeg| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr (hν_le_one aNeg))]
          linarith [hν_nonneg aNeg]
        have hrewrite :
            (1 - δ) * ν aNeg + δ - ν aNeg =
              δ * (1 - ν aNeg) := by ring
        rw [if_pos rfl, hrewrite, abs_mul]
        calc
          |δ| * |1 - ν aNeg| ≤ δ * 1 := by
            rw [abs_of_nonneg hδ_nonneg]
            exact mul_le_mul_of_nonneg_left hbetween hδ_nonneg
          _ = δ := by ring
      · have hbetween : |0 - ν a| ≤ 1 := by
          simp [abs_of_nonneg (hν_nonneg a)]
          exact hν_le_one a
        have hrewrite :
            (1 - δ) * ν a + 0 - ν a =
              δ * (0 - ν a) := by ring
        rw [if_neg h, hrewrite, abs_mul]
        calc
          |δ| * |0 - ν a| ≤ δ * 1 := by
            rw [abs_of_nonneg hδ_nonneg]
            exact mul_le_mul_of_nonneg_left hbetween hδ_nonneg
          _ = δ := by ring
    calc
      |((q a : ℝ) / Q) - ν a|
          ≤ |((q a : ℝ) / Q) - νδ a| + |νδ a - ν a| := by
            have hsplit :
                ((q a : ℝ) / Q) - ν a =
                  (((q a : ℝ) / Q) - νδ a) + (νδ a - ν a) := by
              ring
            rw [hsplit]
            exact abs_add_le _ _
      _ < η + δ := add_lt_add_of_lt_of_le (hqclose_νδ a) hνδ_close
      _ < ε := hclose_total
  · intro a hqa
    rcases hq_support_νδ a hqa with hanchor | hνδ_pos
    · exact Or.inl hanchor
    · by_cases ha : a = aNeg
      · exact Or.inl ha
      · exact Or.inr (by
          have hνδ_eq : νδ a = (1 - δ) * ν a := by
            simp [νδ, ha]
          rw [hνδ_eq] at hνδ_pos
          by_contra hnot
          have hν_zero : ν a = 0 :=
            le_antisymm (le_of_not_gt hnot) (hν_nonneg a)
          simp [hν_zero] at hνδ_pos)

/--
Tail-safe count-vector approximation near a stationary exponential tilt.

This packages the finite rounding/perturbation step for Cramer lower-bound
proofs: a stationary tilt has zero score mean, and perturbing it toward a
negative-score atom gives a strict left-tail empirical type close to the
stationary tilted law.
-/
theorem exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom
    [Nonempty α]
    (μ : PMF α) (score : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0)
    {aNeg : α} (hscoreNeg : score aNeg < 0)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hmargin :
      η * (∑ a : α, |score a|) ≤ δ * (-(score aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ (Q : ℕ) (q : α → ℕ),
      0 < Q ∧
      (∑ a : α, q a = Q) ∧
      (∀ a : α,
        |((q a : ℝ) / Q) -
          (finiteExponentialTilt μ score z a).toReal| < ε) ∧
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
  classical
  let ν : α → ℝ := fun a => (finiteExponentialTilt μ score z a).toReal
  have hν_nonneg : ∀ a, 0 ≤ ν a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hν_sum : ∑ a : α, ν a = 1 := by
    simpa [ν] using pmfToRealSum (finiteExponentialTilt μ score z)
  have hν_mean : ∑ a : α, ν a * score a = 0 := by
    simpa [ν, pmfExp] using
      pmfExp_finiteExponentialTilt_eq_zero_of_stationary
        μ score hstationary
  simpa [ν] using
    exists_countVector_tail_close_to_zero_mean_simplex_via_neg_atom
      ν score hν_nonneg hν_sum hν_mean hscoreNeg
      hδ_nonneg hδ_le_one hη_pos hmargin hclose_total

/--
Denominator-controlled tail-safe count-vector approximation near a stationary
exponential tilt.
-/
theorem exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom_of_large_denominator
    [Nonempty α]
    (μ : PMF α) (score : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0)
    {aNeg : α} (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < η)
    (hmargin :
      η * (∑ a : α, |score a|) ≤ δ * (-(score aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α,
        |((q a : ℝ) / Q) -
          (finiteExponentialTilt μ score z a).toReal| < ε) ∧
      ∑ a : α, (q a : ℝ) * score a ≤ 0 := by
  classical
  let ν : α → ℝ := fun a => (finiteExponentialTilt μ score z a).toReal
  have hν_nonneg : ∀ a, 0 ≤ ν a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hν_sum : ∑ a : α, ν a = 1 := by
    simpa [ν] using pmfToRealSum (finiteExponentialTilt μ score z)
  have hν_mean : ∑ a : α, ν a * score a = 0 := by
    simpa [ν, pmfExp] using
      pmfExp_finiteExponentialTilt_eq_zero_of_stationary
        μ score hstationary
  simpa [ν] using
    exists_countVector_tail_close_to_zero_mean_simplex_via_neg_atom_of_large_denominator
      ν score hν_nonneg hν_sum hν_mean hscoreNeg hQpos
      hδ_nonneg hδ_le_one hη_pos hQ_large hmargin hclose_total

/--
Support-preserving denominator-controlled approximation near a stationary
exponential tilt.  Nonzero rounded counts are guaranteed to lie in the positive
support of the original law.
-/
theorem exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom_of_large_denominator_with_support
    [Nonempty α]
    (μ : PMF α) (score : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0)
    {aNeg : α}
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < η)
    (hmargin :
      η * (∑ a : α, |score a|) ≤ δ * (-(score aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α,
        |((q a : ℝ) / Q) -
          (finiteExponentialTilt μ score z a).toReal| < ε) ∧
      (∑ a : α, (q a : ℝ) * score a ≤ 0) ∧
      ∀ a : α, q a ≠ 0 → 0 < (μ a).toReal := by
  classical
  let ν : α → ℝ := fun a => (finiteExponentialTilt μ score z a).toReal
  have hν_nonneg : ∀ a, 0 ≤ ν a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hν_sum : ∑ a : α, ν a = 1 := by
    simpa [ν] using pmfToRealSum (finiteExponentialTilt μ score z)
  have hν_mean : ∑ a : α, ν a * score a = 0 := by
    simpa [ν, pmfExp] using
      pmfExp_finiteExponentialTilt_eq_zero_of_stationary
        μ score hstationary
  obtain ⟨q, hqsum, hqclose, htail, hq_support⟩ :=
    exists_countVector_tail_close_to_zero_mean_simplex_via_neg_atom_of_large_denominator_with_support
      ν score hν_nonneg hν_sum hν_mean hscoreNeg hQpos
      hδ_nonneg hδ_le_one hη_pos hQ_large hmargin hclose_total
  refine ⟨q, hqsum, ?_, htail, ?_⟩
  · intro a
    simpa [ν] using hqclose a
  · intro a hqa
    rcases hq_support a hqa with hanchor | hν_pos
    · subst a
      exact hmassNeg
    · exact
        (finiteExponentialTilt_apply_toReal_pos_iff
          μ score z a).1 (by simpa [ν] using hν_pos)

/--
Score-gap form of
`exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom`.
-/
theorem exists_countVector_tail_close_to_stationary_tilted_gap_law_via_neg_atom
    [Nonempty α]
    (μ : PMF α) (hiScore loScore : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal *
          ((hiScore a - loScore a) *
            Real.exp (z * (hiScore a - loScore a)))) = 0)
    {aNeg : α} (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hmargin :
      η * (∑ a : α, |hiScore a - loScore a|) ≤
        δ * (-(hiScore aNeg - loScore aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ (Q : ℕ) (q : α → ℕ),
      0 < Q ∧
      (∑ a : α, q a = Q) ∧
      (∀ a : α,
        |((q a : ℝ) / Q) -
          (finiteExponentialTilt μ
            (fun a => hiScore a - loScore a) z a).toReal| < ε) ∧
      ∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0 :=
  exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom
    μ (fun a => hiScore a - loScore a) hstationary hgapNeg
    hδ_nonneg hδ_le_one hη_pos hmargin hclose_total

/--
Denominator-controlled score-gap form of
`exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom`.
-/
theorem exists_countVector_tail_close_to_stationary_tilted_gap_law_via_neg_atom_of_large_denominator
    [Nonempty α]
    (μ : PMF α) (hiScore loScore : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal *
          ((hiScore a - loScore a) *
            Real.exp (z * (hiScore a - loScore a)))) = 0)
    {aNeg : α} (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < η)
    (hmargin :
      η * (∑ a : α, |hiScore a - loScore a|) ≤
        δ * (-(hiScore aNeg - loScore aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α,
        |((q a : ℝ) / Q) -
          (finiteExponentialTilt μ
            (fun a => hiScore a - loScore a) z a).toReal| < ε) ∧
      ∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0 :=
  exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom_of_large_denominator
    μ (fun a => hiScore a - loScore a) hstationary hgapNeg hQpos
    hδ_nonneg hδ_le_one hη_pos hQ_large hmargin hclose_total

/--
Support-preserving denominator-controlled score-gap form of
`exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom`.
-/
theorem exists_countVector_tail_close_to_stationary_tilted_gap_law_via_neg_atom_of_large_denominator_with_support
    [Nonempty α]
    (μ : PMF α) (hiScore loScore : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal *
          ((hiScore a - loScore a) *
            Real.exp (z * (hiScore a - loScore a)))) = 0)
    {aNeg : α}
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q)
    {δ η ε : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_one : δ ≤ 1)
    (hη_pos : 0 < η)
    (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < η)
    (hmargin :
      η * (∑ a : α, |hiScore a - loScore a|) ≤
        δ * (-(hiScore aNeg - loScore aNeg)))
    (hclose_total : η + δ < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α,
        |((q a : ℝ) / Q) -
          (finiteExponentialTilt μ
            (fun a => hiScore a - loScore a) z a).toReal| < ε) ∧
      (∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0) ∧
      ∀ a : α, q a ≠ 0 → 0 < (μ a).toReal :=
  exists_countVector_tail_close_to_stationary_tilted_law_via_neg_atom_of_large_denominator_with_support
    μ (fun a => hiScore a - loScore a) hstationary hmassNeg hgapNeg hQpos
    hδ_nonneg hδ_le_one hη_pos hQ_large hmargin hclose_total

/--
Checkable lower-bound certificate based on exact empirical type masses.

Compared with the older count-vector/path certificate, this includes the
multinomial entropy factor for all samples with the prescribed empirical
counts.
-/
structure FiniteIidScoreEmpiricalTypeLowerCertificate
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  count : (n : ℕ) → α → ℕ
  count_sum : ∀ n : ℕ, ∑ a : α, count n a = n
  count_tail :
    ∀ n : ℕ, ∑ a : α, (count n a : ℝ) * score a ≤ 0
  empirical_type_mass_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        (Nat.multinomial (Finset.univ : Finset α) (count n) : ℝ) *
          ∏ a : α, (μ a).toReal ^ count n a

namespace FiniteIidScoreEmpiricalTypeLowerCertificate

/-- An empirical-type lower certificate gives a direct tail-probability lower certificate. -/
def toTailLowerCertificate
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreEmpiricalTypeLowerCertificate μ score) :
    FiniteIidScoreTailLowerCertificate μ score where
  base := C.base
  lowerConst := C.lowerConst
  degree := C.degree
  base_pos := C.base_pos
  lowerConst_pos := C.lowerConst_pos
  tail_prob_lower := by
    filter_upwards [C.empirical_type_mass_lower] with n hmass
    have htype_prob :
        pmfProb (pmfProduct (Fin n) α μ)
            (fun sample : Fin n → α =>
              ∀ a : α, empiricalCount sample a = C.count n a) =
          (Nat.multinomial (Finset.univ : Finset α) (C.count n) : ℝ) *
            ∏ a : α, (μ a).toReal ^ C.count n a :=
      pmfProduct_prob_empiricalCounts_eq_multinomial
        (μ := μ) (k := C.count n) (C.count_sum n)
    have htype_le_tail :
        pmfProb (pmfProduct (Fin n) α μ)
            (fun sample : Fin n → α =>
              ∀ a : α, empiricalCount sample a = C.count n a) ≤
          finiteIidScoreLeftTailProb μ score 0 n :=
      pmfProduct_prob_empiricalCounts_le_finiteIidScoreLeftTailProb
        (μ := μ) (score := score) (k := C.count n) (C.count_tail n)
    exact hmass.trans (by
      rw [← htype_prob]
      exact htype_le_tail)

/--
An empirical-type lower certificate yields exponential lower bounds at every
slower rate than its geometric base.
-/
theorem hasExpLowerBoundWithConst
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreEmpiricalTypeLowerCertificate μ score)
    {targetRate : ℝ} (htarget : -Real.log C.base < targetRate) :
    HasExpLowerBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate :=
  C.toTailLowerCertificate.hasExpLowerBoundWithConst htarget

/--
Build an empirical-type lower certificate from a periodic empirical type.

This is the entropy-aware analogue of
`FiniteIidScoreCountVectorLowerCertificate.of_periodic`: the one-period
geometric block may include the full multinomial type mass, not only the
single product atom.  Residue coordinates are assigned to a tail-safe filler
atom.
-/
def of_periodic
    {μ : PMF α} {score : α → ℝ}
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤
        (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
          ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal) :
    FiniteIidScoreEmpiricalTypeLowerCertificate μ score where
  base := base
  lowerConst := (μ filler).toReal ^ (Q - 1)
  degree := 0
  base_pos := hbase_pos
  lowerConst_pos := pow_pos hfiller_pos (Q - 1)
  count := periodicCountVector Q q filler
  count_sum := periodicCountVector_sum hQpos q filler hqsum
  count_tail := periodicCountVector_tail score q filler hqtail hfiller_tail
  empirical_type_mass_lower := by
    refine Filter.Eventually.of_forall ?_
    intro n
    let typeMass : ℝ := ∏ a : α, (μ a).toReal ^ q a
    let blockCount : ℝ := Nat.multinomial (Finset.univ : Finset α) q
    let blockMass : ℝ := blockCount * typeMass
    let fillerMass : ℝ := (μ filler).toReal
    have hfiller_nonneg : 0 ≤ fillerMass := hfiller_pos.le
    have hfiller_le_one : fillerMass ≤ 1 := by
      simpa [fillerMass] using pmf_apply_toReal_le_one μ filler
    have hbase_nonneg : 0 ≤ base := hbase_pos.le
    have htype_nonneg : 0 ≤ typeMass := by
      dsimp [typeMass]
      exact Finset.prod_nonneg
        (fun a _ha => pow_nonneg ENNReal.toReal_nonneg _)
    have hblockCount_nonneg : 0 ≤ blockCount := by
      dsimp [blockCount]
      exact_mod_cast Nat.zero_le _
    have hblockMass_nonneg : 0 ≤ blockMass :=
      mul_nonneg hblockCount_nonneg htype_nonneg
    have hblockMass_le_one : blockMass ≤ 1 := by
      let typeEvent : (Fin Q → α) → Prop :=
        fun sample => ∀ a : α, empiricalCount sample a = q a
      have hprob_eq :
          pmfProb (pmfProduct (Fin Q) α μ) typeEvent = blockMass := by
        simpa [typeEvent, blockMass, blockCount, typeMass] using
          (pmfProduct_prob_empiricalCounts_eq_multinomial
            (μ := μ) (n := Q) (k := q) hqsum)
      rw [← hprob_eq]
      exact pmfProb_le_one (pmfProduct (Fin Q) α μ) typeEvent
    have hbase_le_one : base ≤ 1 := by
      have hbase_period_block : base ^ Q ≤ blockMass := by
        simpa [blockMass, blockCount, typeMass] using hbase_period
      have hbase_pow_le_one : base ^ Q ≤ 1 :=
        hbase_period_block.trans hblockMass_le_one
      exact
        (pow_le_one_iff_of_nonneg hbase_pos.le (Nat.ne_of_gt hQpos)).mp
          hbase_pow_le_one
    have hres_lt : n % Q < Q := Nat.mod_lt n hQpos
    have hfiller_residue :
        fillerMass ^ (Q - 1) ≤ fillerMass ^ (n % Q) :=
      real_pow_pred_le_pow_of_lt hfiller_nonneg hfiller_le_one hres_lt
    have hperiod_pow :
        base ^ (Q * (n / Q)) ≤ blockMass ^ (n / Q) := by
      have hpow :
          (base ^ Q) ^ (n / Q) ≤ blockMass ^ (n / Q) :=
        pow_le_pow_left₀ (pow_nonneg hbase_nonneg Q)
          (by simpa [blockMass, blockCount, typeMass] using hbase_period)
          (n / Q)
      simpa [pow_mul] using hpow
    have hQmul_le_n : Q * (n / Q) ≤ n := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n Q
    have hbase_tail :
        base ^ n ≤ base ^ (Q * (n / Q)) :=
      real_pow_antitone_on_unit_interval hbase_nonneg hbase_le_one hQmul_le_n
    have hbase_type :
        base ^ n ≤ blockMass ^ (n / Q) :=
      hbase_tail.trans hperiod_pow
    have hmul :
        fillerMass ^ (Q - 1) * base ^ n ≤
          fillerMass ^ (n % Q) * blockMass ^ (n / Q) :=
      mul_le_mul hfiller_residue hbase_type
        (pow_nonneg hbase_nonneg n)
        (pow_nonneg hfiller_nonneg (n % Q))
    have hblock_expand :
        blockMass ^ (n / Q) =
          blockCount ^ (n / Q) * typeMass ^ (n / Q) := by
      simp [blockMass, mul_pow]
    have hmulti :
        blockCount ^ (n / Q) ≤
          (Nat.multinomial (Finset.univ : Finset α)
            (periodicCountVector Q q filler n) : ℝ) := by
      simpa [blockCount] using
        (multinomial_periodicCountVector_ge_block_pow
          (Q := Q) hQpos q filler hqsum n)
    have htype_pow_nonneg : 0 ≤ typeMass ^ (n / Q) :=
      pow_nonneg htype_nonneg _
    have hfiller_pow_nonneg : 0 ≤ fillerMass ^ (n % Q) :=
      pow_nonneg hfiller_nonneg _
    have hperiodic_mass :
        fillerMass ^ (n % Q) * blockMass ^ (n / Q) ≤
          (Nat.multinomial (Finset.univ : Finset α)
              (periodicCountVector Q q filler n) : ℝ) *
            ∏ a : α, (μ a).toReal ^
              periodicCountVector Q q filler n a := by
      calc
        fillerMass ^ (n % Q) * blockMass ^ (n / Q)
            =
              blockCount ^ (n / Q) *
                (typeMass ^ (n / Q) * fillerMass ^ (n % Q)) := by
              rw [hblock_expand]
              ring
        _ ≤
              (Nat.multinomial (Finset.univ : Finset α)
                  (periodicCountVector Q q filler n) : ℝ) *
                (typeMass ^ (n / Q) * fillerMass ^ (n % Q)) :=
              mul_le_mul_of_nonneg_right hmulti
                (mul_nonneg htype_pow_nonneg hfiller_pow_nonneg)
        _ =
              (Nat.multinomial (Finset.univ : Finset α)
                  (periodicCountVector Q q filler n) : ℝ) *
                ∏ a : α, (μ a).toReal ^
                  periodicCountVector Q q filler n a := by
              rw [periodicCountVector_product_mass_eq]
    change
      fillerMass ^ (Q - 1) * base ^ n /
          (((n.succ : ℕ) : ℝ) ^ 0) ≤
        (Nat.multinomial (Finset.univ : Finset α)
            (periodicCountVector Q q filler n) : ℝ) *
          ∏ a : α, (μ a).toReal ^
            periodicCountVector Q q filler n a
    simpa using hmul.trans hperiodic_mass

/--
Rate-parameterized version of `of_periodic`.

The geometric base is `exp (-baseRate)`, so callers can certify the one-period
block lower bound as `exp (-Q * baseRate) <= blockMass` without introducing a
real root.
-/
def of_periodic_rate
    {μ : PMF α} {score : α → ℝ}
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0)
    {baseRate : ℝ}
    (hbase_period :
      Real.exp (-(Q : ℝ) * baseRate) ≤
        (Nat.multinomial (Finset.univ : Finset α) q : ℝ) *
          ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal) :
    FiniteIidScoreEmpiricalTypeLowerCertificate μ score := by
  refine
    of_periodic (μ := μ) (score := score) hQpos q filler
      hqsum hqtail hfiller_tail (base := Real.exp (-baseRate))
      (Real.exp_pos _) ?_ hfiller_pos
  rw [← Real.exp_nat_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hbase_period

end FiniteIidScoreEmpiricalTypeLowerCertificate

namespace FiniteIidScoreCountVectorLowerCertificate

/--
A count-vector lower certificate is an empirical-type lower certificate.

The empirical-type mass includes the multinomial coefficient, so it is at least
the single count-vector product mass used by the older path/count-vector route.
This lets later large-deviation arguments target the entropy-aware certificate
API while still accepting existing explicit count-vector witnesses.
-/
def toEmpiricalTypeLowerCertificate
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreCountVectorLowerCertificate μ score) :
    FiniteIidScoreEmpiricalTypeLowerCertificate μ score where
  base := C.base
  lowerConst := C.lowerConst
  degree := C.degree
  base_pos := C.base_pos
  lowerConst_pos := C.lowerConst_pos
  count := C.count
  count_sum := C.count_sum
  count_tail := C.count_tail
  empirical_type_mass_lower := by
    filter_upwards [C.count_mass_lower] with n hmass
    have hmulti_ge_one :
        (1 : ℝ) ≤
          (Nat.multinomial (Finset.univ : Finset α) (C.count n) : ℝ) := by
      have hnonempty :
          (empiricalCountEventFinset (α := α) n (C.count n)).Nonempty :=
        empiricalCountEventFinset_nonempty (α := α)
          (C.count n) (C.count_sum n)
      have hcard_pos :
          0 < (empiricalCountEventFinset (α := α) n (C.count n)).card :=
        Finset.card_pos.mpr hnonempty
      have hmulti_pos :
          0 < Nat.multinomial (Finset.univ : Finset α) (C.count n) := by
        rwa [empiricalCountEventFinset_card_eq_multinomial
          (α := α) (C.count n) (C.count_sum n)] at hcard_pos
      exact_mod_cast Nat.succ_le_of_lt hmulti_pos
    have hprod_nonneg :
        0 ≤ ∏ a : α, (μ a).toReal ^ C.count n a :=
      Finset.prod_nonneg
        (fun a _ha => pow_nonneg ENNReal.toReal_nonneg _)
    have hprod_le_type :
        ∏ a : α, (μ a).toReal ^ C.count n a ≤
          (Nat.multinomial (Finset.univ : Finset α) (C.count n) : ℝ) *
            ∏ a : α, (μ a).toReal ^ C.count n a := by
      calc
        ∏ a : α, (μ a).toReal ^ C.count n a
            = (1 : ℝ) *
                ∏ a : α, (μ a).toReal ^ C.count n a := by ring
        _ ≤
            (Nat.multinomial (Finset.univ : Finset α) (C.count n) : ℝ) *
              ∏ a : α, (μ a).toReal ^ C.count n a :=
              mul_le_mul_of_nonneg_right hmulti_ge_one hprod_nonneg
    exact hmass.trans hprod_le_type

end FiniteIidScoreCountVectorLowerCertificate

/-- Empirical-type lower certificate specialized to a candidate-pair score gap. -/
abbrev FiniteIidScoreGapEmpiricalTypeLowerCertificate
    (μ : PMF α) (hiScore loScore : α → ℝ) : Type _ :=
  FiniteIidScoreEmpiricalTypeLowerCertificate μ
    (fun a => hiScore a - loScore a)

/--
Build the finite iid Cramer certificate from an empirical-type lower
certificate, nonnegative mean, and positive-mass support on both sides of zero.
-/
theorem finiteIidScoreCramerCertificate_of_empiricalTypeLower_of_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    (C : FiniteIidScoreEmpiricalTypeLowerCertificate μ score)
    (hrate : -Real.log C.base = finiteChernoffRate μ score) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_tailLower
    μ score
    (finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg)
    C.toTailLowerCertificate
    hrate

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_empiricalTypeLower_of_pos_neg_atoms`.
-/
theorem finiteIidScoreGapCramerCertificate_of_empiricalTypeLower_of_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapEmpiricalTypeLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base =
        finiteChernoffRate μ (fun a => hiScore a - loScore a)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapEmpiricalTypeLowerCertificate] using
    finiteIidScoreCramerCertificate_of_empiricalTypeLower_of_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Build a finite iid Cramer certificate from empirical-type lower-bound
witnesses available at every strictly slower target rate.  Unlike periodic
single-path witnesses, these certificates retain the multinomial entropy
factor of the empirical type.
-/
theorem finiteIidScoreCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    (hlower :
      ∀ targetRate, finiteChernoffRate μ score < targetRate →
        ∃ C : FiniteIidScoreEmpiricalTypeLowerCertificate μ score,
          -Real.log C.base < targetRate) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_tailLower_witnesses
    μ score
    (finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg)
    (fun targetRate htarget => by
      rcases hlower targetRate htarget with ⟨C, hC⟩
      exact ⟨C.toTailLowerCertificate, by simpa using hC⟩)

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms`.
-/
theorem finiteIidScoreGapCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (hlower :
      ∀ targetRate,
        finiteChernoffRate μ (fun a => hiScore a - loScore a) <
          targetRate →
        ∃ C : FiniteIidScoreGapEmpiricalTypeLowerCertificate μ hiScore loScore,
          -Real.log C.base < targetRate) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapEmpiricalTypeLowerCertificate] using
    finiteIidScoreCramerCertificate_of_empiricalTypeLower_witnesses_of_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg hlower

end

end Probability
end AppliedModelingLib
