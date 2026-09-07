import AppliedModelingLib.Foundations.Probability.IIDLargeDeviations
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Vandermonde

open scoped BigOperators
open Filter

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Empirical counts for finite iid products

This file collects reusable finite-product count lemmas that are useful when
lower-bounding iid tail events by a prescribed empirical configuration.
-/

/-- The mass of a finite iid sample regrouped by its empirical counts. -/
theorem pmfProduct_apply_toReal_eq_prod_empiricalCount
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (sample : ι → α) :
    (pmfProduct ι α μ sample).toReal =
      ∏ a : α, (μ a).toReal ^ empiricalCount sample a := by
  classical
  rw [pmfProduct_apply_toReal]
  have hmaps :
      ∀ i ∈ (Finset.univ : Finset ι), sample i ∈ (Finset.univ : Finset α) := by
    simp
  calc
    ∏ i : ι, (μ (sample i)).toReal
        =
        ∏ a : α, ∏ i ∈ (Finset.univ : Finset ι) with sample i = a,
          (μ a).toReal := by
          simpa using
            (Finset.prod_fiberwise_of_maps_to'
              (s := (Finset.univ : Finset ι))
              (t := (Finset.univ : Finset α))
              (g := sample) hmaps
              (f := fun a : α => (μ a).toReal)).symm
    _ =
        ∏ a : α, (μ a).toReal ^ empiricalCount sample a := by
          refine Finset.prod_congr rfl ?_
          intro a _ha
          simp [empiricalCount, successIndexSet, Finset.prod_const]

/--
If `bucket a` is the set of coordinates assigned label `a`, then any sample
matching those buckets has empirical counts equal to the bucket sizes.
-/
theorem empiricalCount_eq_card_bucket_of_forall_mem_bucket
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (bucket : α → Finset ι)
    (hcover : ∀ i : ι, ∃ a : α, i ∈ bucket a)
    (hdisj : ∀ {a b : α}, a ≠ b → Disjoint (bucket a) (bucket b))
    {sample : ι → α}
    (hmatch : ∀ a : α, ∀ i : ι, i ∈ bucket a → sample i = a)
    (a : α) :
    empiricalCount sample a = (bucket a).card := by
  classical
  unfold empiricalCount successIndexSet
  congr 1
  ext i
  constructor
  · intro hi
    have hsample : sample i = a := by
      simpa using (Finset.mem_filter.mp hi).2
    rcases hcover i with ⟨b, hib⟩
    have hb_sample : sample i = b := hmatch b i hib
    have hba : b = a := hb_sample.symm.trans hsample
    simpa [hba] using hib
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmatch a i hi⟩

/--
Exact probability of a fixed finite bucket assignment in an iid product.

The event is that every coordinate in `bucket a` is labeled `a`.  The hypotheses
say that the buckets are a disjoint cover of the index type, so this is the
atom determined by the bucket partition, with its mass regrouped by labels.
-/
theorem pmfProduct_prob_fixedBuckets_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (bucket : α → Finset ι)
    (hcover : ∀ i : ι, ∃ a : α, i ∈ bucket a)
    (hdisj : ∀ {a b : α}, a ≠ b → Disjoint (bucket a) (bucket b)) :
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α =>
          ∀ a : α, ∀ i : ι, i ∈ bucket a → sample i = a) =
      ∏ a : α, (μ a).toReal ^ (bucket a).card := by
  classical
  let coordEvent : ι → α → Prop :=
    fun i x => ∀ a : α, i ∈ bucket a → x = a
  have hevent :
      ∀ sample : ι → α,
        (∀ a : α, ∀ i : ι, i ∈ bucket a → sample i = a) ↔
          ∀ i : ι, coordEvent i (sample i) := by
    intro sample
    constructor
    · intro h i a hia
      exact h a i hia
    · intro h a i hia
      exact h i a hia
  have hcoord_prob :
      ∀ a : α, ∀ i : ι, i ∈ bucket a →
        pmfProb μ (coordEvent i) = (μ a).toReal := by
    intro a i hia
    rw [← pmfProb_singleton μ a]
    refine pmfProb_congr μ ?_
    intro x
    constructor
    · intro hx
      exact hx a hia
    · intro hx b hib
      rw [hx]
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj hne) hia hib)
  have hbucket_union :
      (Finset.univ : Finset α).biUnion bucket = (Finset.univ : Finset ι) := by
    ext i
    simp [hcover i]
  have hpairwise :
      Set.PairwiseDisjoint ((Finset.univ : Finset α) : Set α) bucket := by
    intro a _ha b _hb hne
    exact hdisj hne
  have hprod :
      (∏ i : ι, pmfProb μ (coordEvent i)) =
        ∏ a : α, (μ a).toReal ^ (bucket a).card := by
    calc
      ∏ i : ι, pmfProb μ (coordEvent i)
          =
          ∏ i ∈ (Finset.univ : Finset α).biUnion bucket,
            pmfProb μ (coordEvent i) := by
            rw [hbucket_union]
      _ =
          ∏ a : α, ∏ i ∈ bucket a, pmfProb μ (coordEvent i) := by
            exact Finset.prod_biUnion hpairwise
      _ =
          ∏ a : α, (μ a).toReal ^ (bucket a).card := by
            refine Finset.prod_congr rfl ?_
            intro a _ha
            exact Finset.prod_eq_pow_card (fun i hi => hcoord_prob a i hi)
  calc
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α =>
          ∀ a : α, ∀ i : ι, i ∈ bucket a → sample i = a)
        =
        pmfProb (pmfProduct ι α μ)
          (fun sample : ι → α => ∀ i : ι, coordEvent i (sample i)) := by
          refine pmfProb_congr _ ?_
          intro sample
          exact hevent sample
    _ = ∏ i : ι, pmfProb μ (coordEvent i) :=
          pmfProduct_prob_forall_dependent μ coordEvent
    _ = ∏ a : α, (μ a).toReal ^ (bucket a).card := hprod

/--
A fixed bucket assignment with counts `k` is contained in the empirical-count
event for `k`, giving a reusable lower bound for count events.
-/
theorem pmfProduct_prob_empiricalCounts_ge_fixedBuckets
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (bucket : α → Finset ι) (k : α → ℕ)
    (hcover : ∀ i : ι, ∃ a : α, i ∈ bucket a)
    (hdisj : ∀ {a b : α}, a ≠ b → Disjoint (bucket a) (bucket b))
    (hcard : ∀ a : α, (bucket a).card = k a) :
    ∏ a : α, (μ a).toReal ^ k a ≤
      pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α => ∀ a : α, empiricalCount sample a = k a) := by
  classical
  let fixedEvent : (ι → α) → Prop :=
    fun sample => ∀ a : α, ∀ i : ι, i ∈ bucket a → sample i = a
  let countEvent : (ι → α) → Prop :=
    fun sample => ∀ a : α, empiricalCount sample a = k a
  have hle :
      pmfProb (pmfProduct ι α μ) fixedEvent ≤
        pmfProb (pmfProduct ι α μ) countEvent := by
    refine pmfProb_le_of_imp (pmfProduct ι α μ) fixedEvent countEvent ?_
    intro sample hsample a
    rw [empiricalCount_eq_card_bucket_of_forall_mem_bucket
      bucket hcover hdisj hsample a, hcard a]
  have hfixed :
      pmfProb (pmfProduct ι α μ) fixedEvent =
        ∏ a : α, (μ a).toReal ^ (bucket a).card := by
    simpa [fixedEvent] using
      pmfProduct_prob_fixedBuckets_eq μ bucket hcover hdisj
  have hprod :
      (∏ a : α, (μ a).toReal ^ (bucket a).card) =
        ∏ a : α, (μ a).toReal ^ k a := by
    refine Finset.prod_congr rfl ?_
    intro a _ha
    rw [hcard a]
  rw [hfixed] at hle
  simpa [hprod, countEvent] using hle

/--
A fixed bucket assignment whose score-weighted counts are in the left tail
lower-bounds the iid left-tail probability by its product atom mass.
-/
theorem finiteIidScoreLeftTailProb_ge_fixedBuckets
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ) {n : ℕ}
    (bucket : α → Finset (Fin n))
    (hcover : ∀ i : Fin n, ∃ a : α, i ∈ bucket a)
    (hdisj : ∀ {a b : α}, a ≠ b → Disjoint (bucket a) (bucket b))
    (htail :
      ∑ a : α, ((bucket a).card : ℝ) * score a ≤ 0) :
    ∏ a : α, (μ a).toReal ^ (bucket a).card ≤
      finiteIidScoreLeftTailProb μ score 0 n := by
  classical
  let k : α → ℕ := fun a => (bucket a).card
  calc
    ∏ a : α, (μ a).toReal ^ (bucket a).card
        ≤ pmfProb (pmfProduct (Fin n) α μ)
            (fun sample : Fin n → α =>
              ∀ a : α, empiricalCount sample a = k a) := by
          simpa [k] using
            pmfProduct_prob_empiricalCounts_ge_fixedBuckets
              (μ := μ) (bucket := bucket) (k := k)
              hcover hdisj (fun _a => rfl)
    _ ≤ finiteIidScoreLeftTailProb μ score 0 n := by
          simpa [k] using
            pmfProduct_prob_empiricalCounts_le_finiteIidScoreLeftTailProb
              (μ := μ) (score := score) (k := k) htail

/-- The sigma type associated to a count vector has the prescribed total size. -/
theorem countVectorSigma_card
    {α : Type*} [Fintype α] (k : α → ℕ) {n : ℕ}
    (hk : ∑ a : α, k a = n) :
    Fintype.card (Σ a : α, Fin (k a)) = n := by
  calc
    Fintype.card (Σ a : α, Fin (k a))
        = ∑ a : α, Fintype.card (Fin (k a)) := Fintype.card_sigma
    _ = ∑ a : α, k a := by simp
    _ = n := hk

/-- A canonical equivalence from `Fin n` to the sigma type of a count vector. -/
noncomputable def countVectorSigmaEquiv
    {α : Type*} [Fintype α] (k : α → ℕ) {n : ℕ}
    (hk : ∑ a : α, k a = n) :
    Fin n ≃ (Σ a : α, Fin (k a)) :=
  (Fintype.equivFinOfCardEq (countVectorSigma_card k hk)).symm

/-- The sigma fiber over one label in a count vector. -/
def countVectorSigmaFiber
    {α : Type*} [Fintype α] (k : α → ℕ) (a : α) :
    Finset (Σ b : α, Fin (k b)) :=
  (Finset.univ : Finset (Fin (k a))).map (Function.Embedding.sigmaMk a)

@[simp]
theorem mem_countVectorSigmaFiber
    {α : Type*} [Fintype α] (k : α → ℕ) (a : α)
    (x : Σ b : α, Fin (k b)) :
    x ∈ countVectorSigmaFiber k a ↔ x.1 = a := by
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨i, _hi, hxi⟩
    exact (congrArg Sigma.fst hxi).symm
  · intro hx
    cases x with
    | mk b i =>
        cases hx
        simp [countVectorSigmaFiber]

/--
The canonical bucket partition of `Fin n` induced by a count vector whose
entries sum to `n`.
-/
noncomputable def countVectorBucket
    {α : Type*} [Fintype α] (k : α → ℕ) {n : ℕ}
    (hk : ∑ a : α, k a = n) (a : α) :
    Finset (Fin n) :=
  (countVectorSigmaFiber k a).preimage
    (countVectorSigmaEquiv k hk)
    (countVectorSigmaEquiv k hk).injective.injOn

@[simp]
theorem mem_countVectorBucket
    {α : Type*} [Fintype α] (k : α → ℕ) {n : ℕ}
    (hk : ∑ a : α, k a = n) (a : α) (i : Fin n) :
    i ∈ countVectorBucket k hk a ↔
      (countVectorSigmaEquiv k hk i).1 = a := by
  simp [countVectorBucket]

/-- Count-vector buckets cover all coordinates. -/
theorem countVectorBucket_cover
    {α : Type*} [Fintype α] (k : α → ℕ) {n : ℕ}
    (hk : ∑ a : α, k a = n) :
    ∀ i : Fin n, ∃ a : α, i ∈ countVectorBucket k hk a := by
  intro i
  exact ⟨(countVectorSigmaEquiv k hk i).1, by simp⟩

/-- Distinct count-vector buckets are disjoint. -/
theorem countVectorBucket_disjoint
    {α : Type*} [Fintype α] (k : α → ℕ) {n : ℕ}
    (hk : ∑ a : α, k a = n) :
    ∀ {a b : α}, a ≠ b →
      Disjoint (countVectorBucket k hk a) (countVectorBucket k hk b) := by
  intro a b hab
  rw [Finset.disjoint_left]
  intro i hia hib
  have hia' : (countVectorSigmaEquiv k hk i).1 = a := by
    simpa using hia
  have hib' : (countVectorSigmaEquiv k hk i).1 = b := by
    simpa using hib
  exact hab (hia'.symm.trans hib')

/-- Count-vector buckets have exactly the requested cardinalities. -/
theorem countVectorBucket_card
    {α : Type*} [Fintype α] (k : α → ℕ) {n : ℕ}
    (hk : ∑ a : α, k a = n) (a : α) :
    (countVectorBucket k hk a).card = k a := by
  classical
  unfold countVectorBucket
  rw [Finset.card_preimage]
  simp [countVectorSigmaFiber]

/--
A count vector whose total score is in the left tail lower-bounds the iid
left-tail probability by the product mass of that empirical type.
-/
theorem finiteIidScoreLeftTailProb_ge_countVector
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ) {n : ℕ}
    (k : α → ℕ) (hk : ∑ a : α, k a = n)
    (htail : ∑ a : α, (k a : ℝ) * score a ≤ 0) :
    ∏ a : α, (μ a).toReal ^ k a ≤
      finiteIidScoreLeftTailProb μ score 0 n := by
  classical
  let bucket : α → Finset (Fin n) := countVectorBucket k hk
  have hcard : ∀ a : α, (bucket a).card = k a := by
    intro a
    exact countVectorBucket_card k hk a
  calc
    ∏ a : α, (μ a).toReal ^ k a
        = ∏ a : α, (μ a).toReal ^ (bucket a).card := by
          refine Finset.prod_congr rfl ?_
          intro a _ha
          rw [hcard a]
    _ ≤ finiteIidScoreLeftTailProb μ score 0 n := by
          refine
            finiteIidScoreLeftTailProb_ge_fixedBuckets
              (μ := μ) (score := score) (bucket := bucket)
              (countVectorBucket_cover k hk)
              (countVectorBucket_disjoint k hk)
              ?_
          simpa [bucket, hcard] using htail

/--
For a real base in `[0, 1]`, larger natural exponents give smaller powers.
-/
theorem real_pow_antitone_on_unit_interval
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {m n : ℕ} (hmn : m ≤ n) :
    x ^ n ≤ x ^ m := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  rw [pow_add]
  have hxk : x ^ k ≤ 1 := pow_le_one₀ hx0 hx1
  exact
    mul_le_of_le_one_right (pow_nonneg hx0 m) hxk

/--
If `0 <= x <= 1` and `r < Q`, then the worst residue exponent is `Q - 1`.
-/
theorem real_pow_pred_le_pow_of_lt
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {r Q : ℕ} (hr : r < Q) :
    x ^ (Q - 1) ≤ x ^ r :=
  real_pow_antitone_on_unit_interval hx0 hx1 (Nat.le_pred_of_lt hr)

/--
Periodic count vector obtained by repeating a period count vector `q` and
placing the residue coordinates into a tail-safe filler atom.
-/
def periodicCountVector
    {α : Type*} [DecidableEq α]
    (Q : ℕ) (q : α → ℕ) (filler : α) (n : ℕ) (a : α) : ℕ :=
  (n / Q) * q a + if a = filler then n % Q else 0

/-- The periodic count vector has total size `n`. -/
theorem periodicCountVector_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q) (n : ℕ) :
    ∑ a : α, periodicCountVector Q q filler n a = n := by
  classical
  unfold periodicCountVector
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ a : α, (n / Q) * q a) =
        (n / Q) * ∑ a : α, q a := by
    rw [Finset.mul_sum]
  have hsecond :
      (∑ a : α, (if a = filler then n % Q else 0)) = n % Q := by
    simp
  rw [hfirst, hsecond, hqsum]
  simpa [Nat.mul_comm] using Nat.div_add_mod n Q

/--
If the period count vector is in the left tail and the filler atom is
tail-safe, every periodic count vector is in the left tail.
-/
theorem periodicCountVector_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℝ) {Q : ℕ} (q : α → ℕ) (filler : α)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0) (n : ℕ) :
    ∑ a : α,
        (periodicCountVector Q q filler n a : ℝ) * score a ≤ 0 := by
  classical
  unfold periodicCountVector
  let residue : α → ℕ := fun a => if a = filler then n % Q else 0
  have hsplit :
      (∑ a : α,
          (((n / Q) * q a + residue a : ℕ) : ℝ) *
            score a) =
        ((n / Q : ℕ) : ℝ) * (∑ a : α, (q a : ℝ) * score a) +
          ((n % Q : ℕ) : ℝ) * score filler := by
    calc
      (∑ a : α,
          (((n / Q) * q a + residue a : ℕ) : ℝ) *
            score a)
          =
          ∑ a : α,
            ((((n / Q : ℕ) * q a : ℕ) : ℝ) * score a +
              ((residue a : ℕ) : ℝ) * score a) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [Nat.cast_add]
            ring
      _ =
          (∑ a : α, (((n / Q : ℕ) * q a : ℕ) : ℝ) * score a) +
            ∑ a : α,
              ((residue a : ℕ) : ℝ) * score a := by
            rw [Finset.sum_add_distrib]
      _ =
          ((n / Q : ℕ) : ℝ) * (∑ a : α, (q a : ℝ) * score a) +
            ((n % Q : ℕ) : ℝ) * score filler := by
            congr 1
            · calc
                (∑ a : α, (((n / Q : ℕ) * q a : ℕ) : ℝ) * score a)
                    = ∑ a : α, ((n / Q : ℕ) : ℝ) * ((q a : ℝ) * score a) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _ha
                      rw [Nat.cast_mul]
                      ring
                _ = ((n / Q : ℕ) : ℝ) * (∑ a : α, (q a : ℝ) * score a) := by
                      rw [Finset.mul_sum]
            · simp [residue]
  rw [hsplit]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hqtail)
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hfiller_tail)

/-- Product mass of a periodic count vector. -/
theorem periodicCountVector_product_mass_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) {Q : ℕ} (q : α → ℕ) (filler : α) (n : ℕ) :
    (∏ a : α, (μ a).toReal ^ periodicCountVector Q q filler n a) =
      (∏ a : α, (μ a).toReal ^ q a) ^ (n / Q) *
        (μ filler).toReal ^ (n % Q) := by
  classical
  unfold periodicCountVector
  calc
    (∏ a : α, (μ a).toReal ^
        ((n / Q) * q a + if a = filler then n % Q else 0))
        =
        ∏ a : α,
          ((μ a).toReal ^ ((n / Q) * q a) *
            (μ a).toReal ^ (if a = filler then n % Q else 0)) := by
          refine Finset.prod_congr rfl ?_
          intro a _ha
          rw [pow_add]
    _ =
        (∏ a : α, (μ a).toReal ^ ((n / Q) * q a)) *
          ∏ a : α, (μ a).toReal ^ (if a = filler then n % Q else 0) := by
          rw [Finset.prod_mul_distrib]
    _ =
        (∏ a : α, ((μ a).toReal ^ q a) ^ (n / Q)) *
          (μ filler).toReal ^ (n % Q) := by
          congr 1
          · refine Finset.prod_congr rfl ?_
            intro a _ha
            rw [Nat.mul_comm, pow_mul]
          · simp
    _ =
        (∏ a : α, (μ a).toReal ^ q a) ^ (n / Q) *
          (μ filler).toReal ^ (n % Q) := by
          rw [Finset.prod_pow]

/-- A binomial coefficient is supermultiplicative under adding successes and failures. -/
theorem choose_mul_choose_le_choose_add
    (a b c d : ℕ) :
    (a + b).choose a * (c + d).choose c ≤
      (a + c + (b + d)).choose (a + c) := by
  classical
  have hmem : (a, c) ∈ Finset.antidiagonal (a + c) := by
    simp [Finset.mem_antidiagonal]
  have hterm :
      (a + b).choose a * (c + d).choose c ≤
        ∑ ij ∈ Finset.antidiagonal (a + c),
          (a + b).choose ij.1 * (c + d).choose ij.2 := by
    exact
      Finset.single_le_sum
        (s := Finset.antidiagonal (a + c))
        (f := fun ij : ℕ × ℕ =>
          (a + b).choose ij.1 * (c + d).choose ij.2)
        (fun _ _ => Nat.zero_le _)
        hmem
  have hvand :
      ((a + b) + (c + d)).choose (a + c) =
        ∑ ij ∈ Finset.antidiagonal (a + c),
          (a + b).choose ij.1 * (c + d).choose ij.2 :=
    Nat.add_choose_eq (a + b) (c + d) (a + c)
  rw [← hvand] at hterm
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hterm

/-- Multinomial coefficients are supermultiplicative under pointwise addition of counts. -/
theorem multinomial_mul_le_multinomial_add
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → ℕ) :
    Nat.multinomial s f * Nat.multinomial s g ≤
      Nat.multinomial s (fun a => f a + g a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      have hsum_add :
          (∑ i ∈ s, (f i + g i)) =
            (∑ i ∈ s, f i) + ∑ i ∈ s, g i := by
        rw [Finset.sum_add_distrib]
      have hchoose :
          (f a + ∑ i ∈ s, f i).choose (f a) *
              (g a + ∑ i ∈ s, g i).choose (g a) ≤
            ((f a + g a) + ∑ i ∈ s, (f i + g i)).choose
              (f a + g a) := by
        rw [hsum_add]
        exact choose_mul_choose_le_choose_add
          (f a) (∑ i ∈ s, f i) (g a) (∑ i ∈ s, g i)
      rw [Nat.multinomial_insert ha f,
        Nat.multinomial_insert ha g,
        Nat.multinomial_insert ha (fun a => f a + g a)]
      calc
        ((f a + ∑ i ∈ s, f i).choose (f a) *
              Nat.multinomial s f) *
            ((g a + ∑ i ∈ s, g i).choose (g a) *
              Nat.multinomial s g)
            =
              ((f a + ∑ i ∈ s, f i).choose (f a) *
                  (g a + ∑ i ∈ s, g i).choose (g a)) *
                (Nat.multinomial s f * Nat.multinomial s g) := by
              ring
        _ ≤
              ((f a + g a) + ∑ i ∈ s, (f i + g i)).choose
                  (f a + g a) *
                Nat.multinomial s (fun a => f a + g a) := by
              exact Nat.mul_le_mul hchoose ih

/--
Repeating the same count vector `m` times gives at least the `m`th power of
the one-block multinomial coefficient.
-/
theorem multinomial_pow_le_multinomial_const_mul
    {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → ℕ) (m : ℕ) :
    Nat.multinomial s q ^ m ≤
      Nat.multinomial s (fun a => m * q a) := by
  classical
  induction m with
  | zero =>
      simp [Nat.multinomial]
  | succ m ih =>
      calc
        Nat.multinomial s q ^ (m + 1)
            = Nat.multinomial s q * Nat.multinomial s q ^ m := by
              rw [pow_succ']
        _ ≤ Nat.multinomial s q *
              Nat.multinomial s (fun a => m * q a) := by
              exact Nat.mul_le_mul_left _ ih
        _ ≤ Nat.multinomial s (fun a => q a + m * q a) := by
              exact multinomial_mul_le_multinomial_add
                (s := s) q (fun a => m * q a)
        _ = Nat.multinomial s (fun a => (m + 1) * q a) := by
              refine Nat.multinomial_congr ?_
              intro a ha
              rw [Nat.add_mul, Nat.one_mul]
              exact Nat.add_comm _ _

/--
Adding all residue mass to one atom cannot reduce the repeated-block
multinomial coefficient.
-/
theorem multinomial_const_mul_le_periodicCountVector
    {α : Type*} [Fintype α] [DecidableEq α]
    (Q : ℕ) (q : α → ℕ) (filler : α) (n : ℕ) :
    Nat.multinomial (Finset.univ : Finset α) (fun a => (n / Q) * q a) ≤
      Nat.multinomial (Finset.univ : Finset α)
        (periodicCountVector Q q filler n) := by
  classical
  let residue : α → ℕ := fun a => if a = filler then n % Q else 0
  have hresidue :
      Nat.multinomial (Finset.univ : Finset α) residue = 1 := by
    have hresidue_eq : residue = Pi.single filler (n % Q) := by
      funext a
      by_cases ha : a = filler
      · rw [ha]
        simp [residue, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne ha]
        simp [residue, ha]
    rw [hresidue_eq]
    exact
      Nat.multinomial_single
        (s := (Finset.univ : Finset α)) (a := filler) (n := n % Q)
  have hadd :=
    multinomial_mul_le_multinomial_add
      (s := (Finset.univ : Finset α))
      (fun a => (n / Q) * q a) residue
  rw [hresidue, Nat.mul_one] at hadd
  refine hadd.trans_eq ?_
  refine Nat.multinomial_congr ?_
  intro a _ha
  simp [periodicCountVector, residue]

/--
Nat-valued entropy factor for a periodic empirical type: its multinomial
coefficient contains one block-multinomial factor for each complete period.
-/
theorem multinomial_block_pow_le_periodicCountVector
    {α : Type*} [Fintype α] [DecidableEq α]
    (Q : ℕ) (q : α → ℕ) (filler : α) (n : ℕ) :
    Nat.multinomial (Finset.univ : Finset α) q ^ (n / Q) ≤
      Nat.multinomial (Finset.univ : Finset α)
        (periodicCountVector Q q filler n) :=
  (multinomial_pow_le_multinomial_const_mul
      (s := (Finset.univ : Finset α)) q (n / Q)).trans
    (multinomial_const_mul_le_periodicCountVector Q q filler n)

/--
Entropy factor for a periodic empirical type, in the real-valued form used by
probability lower bounds.
-/
theorem multinomial_periodicCountVector_ge_block_pow
    {α : Type*} [Fintype α] [DecidableEq α]
    {Q : ℕ} (_hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (_hqsum : ∑ a : α, q a = Q) (n : ℕ) :
    (Nat.multinomial (Finset.univ : Finset α)
        (periodicCountVector Q q filler n) : ℝ) ≥
      (Nat.multinomial (Finset.univ : Finset α) q : ℝ) ^ (n / Q) := by
  change
    (Nat.multinomial (Finset.univ : Finset α) q : ℝ) ^ (n / Q) ≤
      (Nat.multinomial (Finset.univ : Finset α)
        (periodicCountVector Q q filler n) : ℝ)
  exact_mod_cast
    (multinomial_block_pow_le_periodicCountVector
      (Q := Q) (q := q) (filler := filler) (n := n))

/--
Checkable lower-bound certificate based on explicit finite bucket partitions.

For each sample size `n`, `bucket n a` assigns coordinates to signal `a`.
The buckets must be a disjoint cover, their weighted counts must force the
left-tail inequality, and the resulting product atom mass must have a
polynomially corrected geometric lower bound.
-/
structure FiniteIidScoreBucketLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  bucket : (n : ℕ) → α → Finset (Fin n)
  cover :
    ∀ n : ℕ, ∀ i : Fin n, ∃ a : α, i ∈ bucket n a
  disjoint :
    ∀ n : ℕ, ∀ {a b : α},
      a ≠ b → Disjoint (bucket n a) (bucket n b)
  bucket_tail :
    ∀ n : ℕ,
      ∑ a : α, ((bucket n a).card : ℝ) * score a ≤ 0
  bucket_mass_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        ∏ a : α, (μ a).toReal ^ (bucket n a).card

namespace FiniteIidScoreBucketLowerCertificate

/-- The canonical sample selected from a bucket lower certificate. -/
def sample
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    (n : ℕ) (i : Fin n) : α :=
  Classical.choose (C.cover n i)

theorem sample_mem_bucket
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    (n : ℕ) (i : Fin n) :
    i ∈ C.bucket n (C.sample n i) :=
  Classical.choose_spec (C.cover n i)

theorem sample_eq_of_mem_bucket
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    {n : ℕ} {a : α} {i : Fin n}
    (hi : i ∈ C.bucket n a) :
    C.sample n i = a := by
  classical
  by_contra hne
  exact
    (Finset.disjoint_left.mp (C.disjoint n hne)
      (C.sample_mem_bucket n i) hi)

/--
The selected canonical sample has exactly the bucket counts prescribed by the
certificate.
-/
theorem empiricalCount_sample_eq_card_bucket
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    (n : ℕ) (a : α) :
    empiricalCount (C.sample n) a = (C.bucket n a).card := by
  classical
  exact
    empiricalCount_eq_card_bucket_of_forall_mem_bucket
      (bucket := C.bucket n)
      (hcover := C.cover n)
      (hdisj := C.disjoint n)
      (sample := C.sample n)
      (fun a i hi => C.sample_eq_of_mem_bucket hi)
      a

/-- The canonical sample selected from a bucket certificate is in the left tail. -/
theorem sample_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    (n : ℕ) :
    finiteIidScoreSum score (C.sample n) ≤ 0 := by
  classical
  rw [finiteIidScoreSum_eq_sum_empiricalCount]
  calc
    ∑ a : α, (empiricalCount (C.sample n) a : ℝ) * score a
        = ∑ a : α, ((C.bucket n a).card : ℝ) * score a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [C.empiricalCount_sample_eq_card_bucket n a]
    _ ≤ 0 := C.bucket_tail n

/--
The canonical sample's product mass is the product mass of the prescribed
buckets.
-/
theorem sample_mass_eq_bucket_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    (n : ℕ) :
    (pmfProduct (Fin n) α μ (C.sample n)).toReal =
      ∏ a : α, (μ a).toReal ^ (C.bucket n a).card := by
  classical
  rw [pmfProduct_apply_toReal_eq_prod_empiricalCount]
  refine Finset.prod_congr rfl ?_
  intro a _ha
  rw [C.empiricalCount_sample_eq_card_bucket n a]

/-- A bucket lower certificate is a path lower certificate. -/
def toPathLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score) :
    FiniteIidScorePathLowerCertificate μ score where
  base := C.base
  lowerConst := C.lowerConst
  degree := C.degree
  base_pos := C.base_pos
  lowerConst_pos := C.lowerConst_pos
  sample := C.sample
  sample_tail := C.sample_tail
  sample_mass_lower := by
    filter_upwards [C.bucket_mass_lower] with n hmass
    rw [C.sample_mass_eq_bucket_mass n]
    exact hmass

/--
A bucket lower certificate yields exponential lower bounds at every slower rate
than its geometric base.
-/
theorem hasExpLowerBoundWithConst
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreBucketLowerCertificate μ score)
    {targetRate : ℝ} (htarget : -Real.log C.base < targetRate) :
    HasExpLowerBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate :=
  C.toPathLowerCertificate.hasExpLowerBoundWithConst htarget

end FiniteIidScoreBucketLowerCertificate

/-- Bucket lower certificate specialized to a candidate-pair score gap. -/
abbrev FiniteIidScoreGapBucketLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (hiScore loScore : α → ℝ) : Type _ :=
  FiniteIidScoreBucketLowerCertificate μ
    (fun a => hiScore a - loScore a)

/--
Checkable lower-bound certificate based on explicit empirical count vectors.

This is usually the most convenient finite-type object: for each sample size
`n`, provide counts summing to `n`, prove the count-weighted score lies in the
left tail, and prove a polynomially corrected geometric lower bound on the
product mass of that type.  The sigma-bucket constructor above turns this into
the bucket/path certificates used by exact-rate endpoints.
-/
structure FiniteIidScoreCountVectorLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
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
  count_mass_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        ∏ a : α, (μ a).toReal ^ count n a

namespace FiniteIidScoreCountVectorLowerCertificate

/-- A count-vector lower certificate is a bucket lower certificate. -/
def toBucketLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreCountVectorLowerCertificate μ score) :
    FiniteIidScoreBucketLowerCertificate μ score where
  base := C.base
  lowerConst := C.lowerConst
  degree := C.degree
  base_pos := C.base_pos
  lowerConst_pos := C.lowerConst_pos
  bucket := fun n => countVectorBucket (C.count n) (C.count_sum n)
  cover := fun n => countVectorBucket_cover (C.count n) (C.count_sum n)
  disjoint := fun n => countVectorBucket_disjoint (C.count n) (C.count_sum n)
  bucket_tail := by
    intro n
    have hsum :
        (∑ a : α,
            (((countVectorBucket (C.count n) (C.count_sum n) a).card : ℝ) *
              score a)) =
          ∑ a : α, (C.count n a : ℝ) * score a := by
      refine Finset.sum_congr rfl ?_
      intro a _ha
      rw [countVectorBucket_card (C.count n) (C.count_sum n) a]
    rw [hsum]
    exact C.count_tail n
  bucket_mass_lower := by
    filter_upwards [C.count_mass_lower] with n hmass
    have hprod :
        (∏ a : α, (μ a).toReal ^ C.count n a) =
          ∏ a : α,
            (μ a).toReal ^
              (countVectorBucket (C.count n) (C.count_sum n) a).card := by
      refine Finset.prod_congr rfl ?_
      intro a _ha
      rw [countVectorBucket_card (C.count n) (C.count_sum n) a]
    rw [← hprod]
    exact hmass

/-- A count-vector lower certificate is a path lower certificate. -/
def toPathLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreCountVectorLowerCertificate μ score) :
    FiniteIidScorePathLowerCertificate μ score :=
  C.toBucketLowerCertificate.toPathLowerCertificate

/--
A count-vector lower certificate yields exponential lower bounds at every
slower rate than its geometric base.
-/
theorem hasExpLowerBoundWithConst
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreCountVectorLowerCertificate μ score)
    {targetRate : ℝ} (htarget : -Real.log C.base < targetRate) :
    HasExpLowerBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate :=
  C.toPathLowerCertificate.hasExpLowerBoundWithConst htarget

/--
Build a count-vector lower certificate from a periodic empirical type.

The period counts `q` sum to `Q` and lie in the left tail.  For sample size
`n`, the construction repeats `q` `n / Q` times and assigns the residue
coordinates to a tail-safe filler atom.  The geometric base is supplied through
`base ^ Q <=` the one-period product mass, which lets callers choose a
closed-form root without this theorem depending on real-root algebra.
-/
def of_periodic
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal) :
    FiniteIidScoreCountVectorLowerCertificate μ score where
  base := base
  lowerConst := (μ filler).toReal ^ (Q - 1)
  degree := 0
  base_pos := hbase_pos
  lowerConst_pos := pow_pos hfiller_pos (Q - 1)
  count := periodicCountVector Q q filler
  count_sum := periodicCountVector_sum hQpos q filler hqsum
  count_tail := periodicCountVector_tail score q filler hqtail hfiller_tail
  count_mass_lower := by
    refine Filter.Eventually.of_forall ?_
    intro n
    let typeMass : ℝ := ∏ a : α, (μ a).toReal ^ q a
    let fillerMass : ℝ := (μ filler).toReal
    have hfiller_nonneg : 0 ≤ fillerMass := hfiller_pos.le
    have hfiller_le_one : fillerMass ≤ 1 := by
      simpa [fillerMass] using pmf_apply_toReal_le_one μ filler
    have hbase_nonneg : 0 ≤ base := hbase_pos.le
    have htype_nonneg : 0 ≤ typeMass := by
      dsimp [typeMass]
      exact Finset.prod_nonneg
        (fun a _ha => pow_nonneg ENNReal.toReal_nonneg _)
    have htype_le_one : typeMass ≤ 1 := by
      dsimp [typeMass]
      exact Finset.prod_le_one
        (fun a _ha => pow_nonneg ENNReal.toReal_nonneg _)
        (fun a _ha =>
          pow_le_one₀ ENNReal.toReal_nonneg (pmf_apply_toReal_le_one μ a))
    have hbase_le_one : base ≤ 1 := by
      have hbase_period_type : base ^ Q ≤ typeMass := by
        simpa [typeMass] using hbase_period
      have hbase_pow_le_one : base ^ Q ≤ 1 :=
        hbase_period_type.trans htype_le_one
      exact
        (pow_le_one_iff_of_nonneg hbase_pos.le (Nat.ne_of_gt hQpos)).mp
          hbase_pow_le_one
    have hres_lt : n % Q < Q := Nat.mod_lt n hQpos
    have hfiller_residue :
        fillerMass ^ (Q - 1) ≤ fillerMass ^ (n % Q) :=
      real_pow_pred_le_pow_of_lt hfiller_nonneg hfiller_le_one hres_lt
    have hperiod_pow :
        base ^ (Q * (n / Q)) ≤ typeMass ^ (n / Q) := by
      have hpow :
          (base ^ Q) ^ (n / Q) ≤ typeMass ^ (n / Q) :=
        pow_le_pow_left₀ (pow_nonneg hbase_nonneg Q)
          (by simpa [typeMass] using hbase_period) (n / Q)
      simpa [pow_mul] using hpow
    have hQmul_le_n : Q * (n / Q) ≤ n := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n Q
    have hbase_tail :
        base ^ n ≤ base ^ (Q * (n / Q)) :=
      real_pow_antitone_on_unit_interval hbase_nonneg hbase_le_one hQmul_le_n
    have hbase_type :
        base ^ n ≤ typeMass ^ (n / Q) :=
      hbase_tail.trans hperiod_pow
    have hmul :
        fillerMass ^ (Q - 1) * base ^ n ≤
          fillerMass ^ (n % Q) * typeMass ^ (n / Q) :=
      mul_le_mul hfiller_residue hbase_type
        (pow_nonneg hbase_nonneg n)
        (pow_nonneg hfiller_nonneg (n % Q))
    change
      fillerMass ^ (Q - 1) * base ^ n /
          (((n.succ : ℕ) : ℝ) ^ 0) ≤
        ∏ a : α, (μ a).toReal ^ periodicCountVector Q q filler n a
    rw [periodicCountVector_product_mass_eq]
    simpa [typeMass, fillerMass, mul_comm, mul_left_comm, mul_assoc] using hmul

end FiniteIidScoreCountVectorLowerCertificate

/-- Count-vector lower certificate specialized to a candidate-pair score gap. -/
abbrev FiniteIidScoreGapCountVectorLowerCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (hiScore loScore : α → ℝ) : Type _ :=
  FiniteIidScoreCountVectorLowerCertificate μ
    (fun a => hiScore a - loScore a)

/--
Build the finite iid Cramer certificate from a count-vector lower certificate,
nonnegative mean, and positive-mass support on both sides of zero.
-/
theorem finiteIidScoreCramerCertificate_of_countVectorLower_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    (C : FiniteIidScoreCountVectorLowerCertificate μ score)
    (hrate : -Real.log C.base = finiteChernoffRate μ score) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_pathLower
    μ score
    (finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg)
    C.toPathLowerCertificate
    hrate

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_countVectorLower_of_pos_neg_atoms`.
-/
theorem finiteIidScoreGapCramerCertificate_of_countVectorLower_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapCountVectorLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base =
        finiteChernoffRate μ (fun a => hiScore a - loScore a)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapCountVectorLowerCertificate] using
    finiteIidScoreCramerCertificate_of_countVectorLower_of_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg C hrate

/--
Build the finite iid Cramer certificate directly from periodic empirical-count
data, nonnegative mean, and positive-mass support on both sides of zero.
-/
theorem finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hrate : -Real.log base = finiteChernoffRate μ score) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_countVectorLower_of_pos_neg_atoms
    μ score hmean hmassPos hscorePos hmassNeg hscoreNeg
    (FiniteIidScoreCountVectorLowerCertificate.of_periodic
      μ score hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos)
    hrate

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_pos_neg_atoms`.
-/
theorem finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail :
      ∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hrate :
      -Real.log base =
        finiteChernoffRate μ (fun a => hiScore a - loScore a)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hrate

/--
Build a finite iid Cramer certificate from periodic empirical-count data plus
a certified global finite log-MGF minimizer for the resulting geometric base.
-/
theorem finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_global_min
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hmin : ∀ z : ℝ, Real.log base ≤ finiteLogMGF μ score z)
    (hwitness : finiteLogMGF μ score z0 = Real.log base) :
    FiniteIidScoreCramerCertificate μ score := by
  have hrate : -Real.log base = finiteChernoffRate μ score := by
    rw [finiteChernoffRate_eq_neg_log_base_of_logMGF_global_min
      μ score hmin hwitness]
  exact
    finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hrate

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_global_min`.
-/
theorem finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_logMGF_global_min
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail :
      ∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hmin :
      ∀ z : ℝ,
        Real.log base ≤
          finiteLogMGF μ (fun a => hiScore a - loScore a) z)
    (hwitness :
      finiteLogMGF μ (fun a => hiScore a - loScore a) z0 =
        Real.log base) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_global_min
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hmin hwitness

/--
Build a finite iid Cramer certificate from periodic empirical-count data plus
a first-order finite log-MGF minimizer certificate.  Finite log-MGF convexity
is supplied by the shared finite-support theorem.
-/
theorem finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_deriv_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hderiv : HasDerivAt (fun z : ℝ => finiteLogMGF μ score z) 0 z0)
    (hwitness : finiteLogMGF μ score z0 = Real.log base) :
    FiniteIidScoreCramerCertificate μ score := by
  have hmin :
      ∀ z : ℝ, Real.log base ≤ finiteLogMGF μ score z := by
    intro z
    have hmin_at_z0 :=
      finiteLogMGF_global_min_of_convex_hasDerivAt_zero
        μ score (finiteLogMGF_convex μ score) hderiv z
    simpa [hwitness] using hmin_at_z0
  exact
    finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_global_min
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hmin hwitness

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_deriv_zero`.
-/
theorem finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_logMGF_deriv_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail :
      ∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          finiteLogMGF μ (fun a => hiScore a - loScore a) z)
        0 z0)
    (hwitness :
      finiteLogMGF μ (fun a => hiScore a - loScore a) z0 =
        Real.log base) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_deriv_zero
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hderiv hwitness

/--
Build a finite iid Cramer certificate from periodic empirical-count data plus
the explicit stationary equation for the finite log-MGF minimizer.
-/
theorem finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_stationary
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail : ∑ a : α, (q a : ℝ) * score a ≤ 0)
    (hfiller_tail : score filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z0 * score a))) = 0)
    (hwitness : finiteLogMGF μ score z0 = Real.log base) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_logMGF_deriv_zero
    μ score hmean hmassPos hscorePos hmassNeg hscoreNeg
    hQpos q filler hqsum hqtail hfiller_tail
    hbase_pos hbase_period hfiller_pos
    (finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
      μ score hstationary)
    hwitness

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_stationary`.
-/
theorem finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_of_stationary
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {Q : ℕ} (hQpos : 0 < Q) (q : α → ℕ) (filler : α)
    (hqsum : ∑ a : α, q a = Q)
    (hqtail :
      ∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0)
    (hfiller_tail : hiScore filler - loScore filler ≤ 0)
    {base z0 : ℝ}
    (hbase_pos : 0 < base)
    (hbase_period :
      base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a)
    (hfiller_pos : 0 < (μ filler).toReal)
    (hstationary :
      (∑ a : α,
        (μ a).toReal *
          ((hiScore a - loScore a) *
            Real.exp (z0 * (hiScore a - loScore a)))) = 0)
    (hwitness :
      finiteLogMGF μ (fun a => hiScore a - loScore a) z0 =
        Real.log base) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_periodic_countVectorLower_of_stationary
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg
      hQpos q filler hqsum hqtail hfiller_tail
      hbase_pos hbase_period hfiller_pos hstationary hwitness

/--
Build a finite iid Cramer certificate from count-vector lower-bound witnesses
available at every strictly slower target rate, with the Chernoff upper side
discharged by nonnegative mean and positive-mass atoms on both sides of zero.
-/
theorem finiteIidScoreCramerCertificate_of_countVectorLower_witnesses_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    (hlower :
      ∀ targetRate, finiteChernoffRate μ score < targetRate →
        ∃ C : FiniteIidScoreCountVectorLowerCertificate μ score,
          -Real.log C.base < targetRate) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_pathLower_witnesses
    μ score
    (finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg)
    (fun targetRate htarget => by
      rcases hlower targetRate htarget with ⟨C, hC⟩
      exact ⟨C.toPathLowerCertificate, by simpa using hC⟩)

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_countVectorLower_witnesses_of_pos_neg_atoms`.
-/
theorem finiteIidScoreGapCramerCertificate_of_countVectorLower_witnesses_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
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
        ∃ C : FiniteIidScoreGapCountVectorLowerCertificate μ hiScore loScore,
          -Real.log C.base < targetRate) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapCountVectorLowerCertificate] using
    finiteIidScoreCramerCertificate_of_countVectorLower_witnesses_of_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg hlower

/--
Build a finite iid Cramer certificate from periodic empirical-count witnesses
available at every strictly slower target rate.
-/
theorem finiteIidScoreCramerCertificate_of_periodic_countVectorLower_witnesses_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    (hlower :
      ∀ targetRate, finiteChernoffRate μ score < targetRate →
        ∃ (Q : ℕ) (q : α → ℕ) (filler : α) (base : ℝ),
          0 < Q ∧
          (∑ a : α, q a = Q) ∧
          (∑ a : α, (q a : ℝ) * score a ≤ 0) ∧
          score filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a ∧
          0 < (μ filler).toReal ∧
          -Real.log base < targetRate) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_countVectorLower_witnesses_of_pos_neg_atoms
    μ score hmean hmassPos hscorePos hmassNeg hscoreNeg
    (fun targetRate htarget => by
      rcases hlower targetRate htarget with
        ⟨Q, q, filler, base, hQpos, hqsum, hqtail, hfiller_tail,
          hbase_pos, hbase_period, hfiller_pos, hbase_rate⟩
      refine
        ⟨FiniteIidScoreCountVectorLowerCertificate.of_periodic
          μ score hQpos q filler hqsum hqtail hfiller_tail
          hbase_pos hbase_period hfiller_pos, ?_⟩
      exact hbase_rate)

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_periodic_countVectorLower_witnesses_of_pos_neg_atoms`.
-/
theorem finiteIidScoreGapCramerCertificate_of_periodic_countVectorLower_witnesses_of_pos_neg_atoms
    {α : Type*} [Fintype α] [DecidableEq α]
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
        ∃ (Q : ℕ) (q : α → ℕ) (filler : α) (base : ℝ),
          0 < Q ∧
          (∑ a : α, q a = Q) ∧
          (∑ a : α, (q a : ℝ) * (hiScore a - loScore a) ≤ 0) ∧
          hiScore filler - loScore filler ≤ 0 ∧
          0 < base ∧
          base ^ Q ≤ ∏ a : α, (μ a).toReal ^ q a ∧
          0 < (μ filler).toReal ∧
          -Real.log base < targetRate) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_periodic_countVectorLower_witnesses_of_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg hlower

end

end Probability
end AppliedModelingLib
