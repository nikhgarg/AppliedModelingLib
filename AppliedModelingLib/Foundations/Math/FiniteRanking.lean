import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite Rankings

Reusable helpers for enumerating a finite set in nondecreasing score order.

## Main declarations

* `FiniteRanking.rankAgentByValue`: enumerate a finite set using the
  lexicographic key `(value, tie-breaker)`.
* `FiniteRanking.rankValueByValue_mono`: the resulting values are monotone in
  the rank index.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace FiniteRanking

open Prod.Lex

/--
Any nonadjacent weak inversion in a real-valued sequence contains an adjacent
weak inversion. This is the deterministic event-inclusion kernel behind
reducing a nonadjacent ranking error to an adjacent ranking error.
-/
theorem exists_adjacent_inversion_of_nonadjacent_inversion
    (x : ℕ → ℝ) {i j : ℕ} (hij : i < j) (hbad : x j ≤ x i) :
    ∃ m : ℕ, i ≤ m ∧ m < j ∧ x (m + 1) ≤ x m := by
  by_contra hnone
  have hstep :
      ∀ m : ℕ, i ≤ m → m < j → x m < x (m + 1) := by
    intro m him hmj
    by_contra hnot
    exact hnone ⟨m, him, hmj, le_of_not_gt hnot⟩
  have hchain : x i < x j := by
    have hsucc : i + 1 ≤ j := Nat.succ_le_of_lt hij
    have hbase : (i + 1 ≤ j → x i < x (i + 1)) := by
      intro _h
      exact hstep i le_rfl hij
    have hind :
        ∀ n : ℕ, i + 1 ≤ n →
          (n ≤ j → x i < x n) → (n + 1 ≤ j → x i < x (n + 1)) := by
      intro n hle ih hn1
      have hn_lt_j : n < j := Nat.lt_of_succ_le hn1
      have hi_le_n : i ≤ n := (Nat.le_succ i).trans hle
      exact (ih hn_lt_j.le).trans (hstep n hi_le_n hn_lt_j)
    exact
      (Nat.le_induction
        (P := fun n _ => n ≤ j → x i < x n)
        hbase hind j hsucc) le_rfl
  exact (not_lt_of_ge hbad) hchain

/--
Finite-index version of
`exists_adjacent_inversion_of_nonadjacent_inversion`.  Any inverted pair in a
finite ranked vector contains an adjacent inverted pair between them.
-/
theorem exists_adjacent_fin_inversion_of_nonadjacent_inversion
    {n : ℕ} (x : Fin n → ℝ) {i j : Fin n}
    (hij : i.val < j.val) (hbad : x j ≤ x i) :
    ∃ (m : Fin n) (hm_succ : m.val + 1 < n),
      i.val ≤ m.val ∧ m.val < j.val ∧
        x ⟨m.val + 1, hm_succ⟩ ≤ x m := by
  let xNat : ℕ → ℝ := fun k => if hk : k < n then x ⟨k, hk⟩ else 0
  have hbadNat : xNat j.val ≤ xNat i.val := by
    simp [xNat, hbad]
  obtain ⟨m, him, hmj, hstep⟩ :=
    exists_adjacent_inversion_of_nonadjacent_inversion xNat hij hbadNat
  have hm_lt_n : m < n := lt_trans hmj j.isLt
  have hm_succ_lt : m + 1 < n :=
    lt_of_le_of_lt (Nat.succ_le_of_lt hmj) j.isLt
  refine ⟨⟨m, hm_lt_n⟩, hm_succ_lt, him, hmj, ?_⟩
  simpa [xNat, hm_lt_n, hm_succ_lt] using hstep

/--
Event-shaped finite ranking kernel: the existence of any inverted pair implies
the existence of an adjacent inverted pair.
-/
theorem exists_adjacent_fin_inversion_of_any_inversion
    {n : ℕ} (x : Fin n → ℝ)
    (hbad : ∃ i j : Fin n, i.val < j.val ∧ x j ≤ x i) :
    ∃ (m : Fin n) (hm_succ : m.val + 1 < n),
      x ⟨m.val + 1, hm_succ⟩ ≤ x m := by
  rcases hbad with ⟨i, j, hij, hbadij⟩
  rcases exists_adjacent_fin_inversion_of_nonadjacent_inversion
      x hij hbadij with
    ⟨m, hm_succ, _him, _hmj, hstep⟩
  exact ⟨m, hm_succ, hstep⟩

/--
Set-inclusion form of the adjacent-inversion kernel for outcome-indexed score
vectors.
-/
theorem anyInversionSet_subset_adjacentInversionSet
    {Ω : Type*} {n : ℕ} (x : Ω → Fin n → ℝ) :
    {ω : Ω | ∃ i j : Fin n, i.val < j.val ∧ x ω j ≤ x ω i} ⊆
      {ω : Ω |
        ∃ (m : Fin n) (hm_succ : m.val + 1 < n),
          x ω ⟨m.val + 1, hm_succ⟩ ≤ x ω m} := by
  intro ω hω
  exact exists_adjacent_fin_inversion_of_any_inversion (x ω) hω

variable {α : Type*} [LinearOrder α] [DecidableEq α]

/-- Lexicographic `(value, tie-breaker)` key used to rank a finite set. -/
def valueTieKey (value : α → ℝ) (a : α) : ℝ ×ₗ α :=
  toLex (value a, a)

theorem valueTieKey_injective (value : α → ℝ) :
    Function.Injective (valueTieKey value) := by
  intro a b h
  have hpair : (value a, a) = (value b, b) := by
    exact toLex_inj.mp h
  exact congrArg Prod.snd hpair

/--
The finite set of lexicographic value/tie-breaker keys associated with a
finite set of alternatives.
-/
noncomputable def valueTieKeySet (s : Finset α) (value : α → ℝ) :
    Finset (ℝ ×ₗ α) :=
  s.image (valueTieKey value)

theorem valueTieKeySet_card (s : Finset α) (value : α → ℝ) :
    (valueTieKeySet s value).card = s.card := by
  classical
  unfold valueTieKeySet
  exact Finset.card_image_of_injective s (valueTieKey_injective value)

/-- The increasing key enumeration of `s` by `(value, tie-breaker)`. -/
noncomputable def rankKeyByValue (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) : Fin k → ℝ ×ₗ α :=
  (valueTieKeySet s value).orderEmbOfFin
    ((valueTieKeySet_card s value).trans hcard)

/-- The agent/alternative at rank `i` in nondecreasing value order. -/
noncomputable def rankAgentByValue (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) : Fin k → α :=
  fun i => (ofLex (rankKeyByValue s value hcard i)).2

/-- The value at rank `i` in nondecreasing value order. -/
noncomputable def rankValueByValue (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) : Fin k → ℝ :=
  fun i => (ofLex (rankKeyByValue s value hcard i)).1

theorem rankKeyByValue_mem (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankKeyByValue s value hcard i ∈ valueTieKeySet s value := by
  classical
  exact Finset.orderEmbOfFin_mem _ _ i

theorem rankKeyByValue_eq_valueTieKey (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankKeyByValue s value hcard i =
      valueTieKey value (rankAgentByValue s value hcard i) := by
  classical
  have hmem := rankKeyByValue_mem s value hcard i
  rcases Finset.mem_image.mp hmem with ⟨a, _ha, hkey⟩
  have hpair :
      ofLex (rankKeyByValue s value hcard i) = (value a, a) := by
    exact (congrArg ofLex hkey).symm
  simpa [rankAgentByValue, hpair] using hkey.symm

theorem rankValueByValue_eq_value (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankValueByValue s value hcard i =
      value (rankAgentByValue s value hcard i) := by
  classical
  have hkey := rankKeyByValue_eq_valueTieKey s value hcard i
  have hpair :
      ofLex (rankKeyByValue s value hcard i) =
        (value (rankAgentByValue s value hcard i),
          rankAgentByValue s value hcard i) := by
    simpa [valueTieKey] using congrArg ofLex hkey
  simpa [rankValueByValue] using congrArg Prod.fst hpair

theorem rankAgentByValue_mem (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankAgentByValue s value hcard i ∈ s := by
  classical
  have hmem := rankKeyByValue_mem s value hcard i
  rcases Finset.mem_image.mp hmem with ⟨a, ha, hkey⟩
  have hpair :
      ofLex (rankKeyByValue s value hcard i) = (value a, a) := by
    exact (congrArg ofLex hkey).symm
  simpa [rankAgentByValue, hpair] using ha

theorem rankValueByValue_mono (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    ∀ r i : Fin k, r.val < i.val →
      rankValueByValue s value hcard r ≤ rankValueByValue s value hcard i := by
  intro r i hri
  have hle_fin : r ≤ i := by
    exact_mod_cast Nat.le_of_lt hri
  have hkey_le :
      rankKeyByValue s value hcard r ≤ rankKeyByValue s value hcard i :=
    ((valueTieKeySet s value).orderEmbOfFin
      ((valueTieKeySet_card s value).trans hcard)).monotone hle_fin
  exact Prod.Lex.monotone_fst _ _ hkey_le

theorem rankAgentByValue_injective (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    Function.Injective (rankAgentByValue s value hcard) := by
  intro i j hij
  have hkey_i := rankKeyByValue_eq_valueTieKey s value hcard i
  have hkey_j := rankKeyByValue_eq_valueTieKey s value hcard j
  have hkey :
      rankKeyByValue s value hcard i =
        rankKeyByValue s value hcard j := by
    rw [hkey_i, hkey_j, hij]
  exact
    ((valueTieKeySet s value).orderEmbOfFin
      ((valueTieKeySet_card s value).trans hcard)).injective hkey

theorem image_rankAgentByValue_univ (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    Finset.image (rankAgentByValue s value hcard) Finset.univ = s := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
    exact rankAgentByValue_mem s value hcard i
  · rw [Finset.card_image_of_injective _ (rankAgentByValue_injective s value hcard)]
    rw [Finset.card_univ, Fintype.card_fin, ← hcard]

/-- Sum a real-valued function over a finite set by its ranked enumeration. -/
theorem sum_rankAgentByValue_eq_sum (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (f : α → ℝ) :
    (∑ i : Fin k, f (rankAgentByValue s value hcard i)) =
      ∑ a ∈ s, f a := by
  classical
  calc
    (∑ i : Fin k, f (rankAgentByValue s value hcard i))
        = (∑ a ∈ Finset.image (rankAgentByValue s value hcard)
          (Finset.univ : Finset (Fin k)), f a) := by
          symm
          exact Finset.sum_image
            (s := (Finset.univ : Finset (Fin k)))
            (f := f)
            (g := rankAgentByValue s value hcard)
            (by
              intro i _hi j _hj hij
              exact rankAgentByValue_injective s value hcard hij)
    _ = ∑ a ∈ s, f a := by
          rw [image_rankAgentByValue_univ s value hcard]

theorem sum_rankValueByValue_eq_sum (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    (∑ i : Fin k, rankValueByValue s value hcard i) =
      ∑ a ∈ s, value a := by
  classical
  calc
    (∑ i : Fin k, rankValueByValue s value hcard i)
        = ∑ i : Fin k, value (rankAgentByValue s value hcard i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact rankValueByValue_eq_value s value hcard i
    _ = (∑ a ∈ Finset.image (rankAgentByValue s value hcard)
          (Finset.univ : Finset (Fin k)), value a) := by
          symm
          exact Finset.sum_image
            (s := (Finset.univ : Finset (Fin k)))
            (f := value)
            (g := rankAgentByValue s value hcard)
            (by
              intro i _hi j _hj hij
              exact rankAgentByValue_injective s value hcard hij)
    _ = ∑ a ∈ s, value a := by
          rw [image_rankAgentByValue_univ s value hcard]

/-- Elements whose sorted rank index lies strictly below `cut`. -/
noncomputable def lowerRankFinset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) : Finset α :=
  ((Finset.univ : Finset (Fin k)).filter fun i => i.val < cut).image
    (rankAgentByValue s value hcard)

/-- Elements whose sorted rank index lies weakly above `cut`. -/
noncomputable def upperRankFinset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) : Finset α :=
  ((Finset.univ : Finset (Fin k)).filter fun i => cut ≤ i.val).image
    (rankAgentByValue s value hcard)

theorem lowerRankFinset_subset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    lowerRankFinset s value hcard cut ⊆ s := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
  exact rankAgentByValue_mem s value hcard i

theorem lowerRankFinset_mono (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) {cut₁ cut₂ : ℕ}
    (hcut : cut₁ ≤ cut₂) :
    lowerRankFinset s value hcard cut₁ ⊆
      lowerRankFinset s value hcard cut₂ := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i,
      Nat.lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hcut⟩

theorem upperRankFinset_subset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    upperRankFinset s value hcard cut ⊆ s := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
  exact rankAgentByValue_mem s value hcard i

theorem lowerRankFinset_disjoint_upperRankFinset
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    ∀ a : α,
      a ∈ lowerRankFinset s value hcard cut →
      a ∈ upperRankFinset s value hcard cut → False := by
  classical
  intro a hlow hhigh
  rcases Finset.mem_image.mp hlow with ⟨lo, hlo, hloeq⟩
  rcases Finset.mem_image.mp hhigh with ⟨hi, hhi, hhieq⟩
  have hagent_eq :
      rankAgentByValue s value hcard lo =
        rankAgentByValue s value hcard hi := by
    rw [hloeq, hhieq]
  have hidx : lo = hi :=
    rankAgentByValue_injective s value hcard hagent_eq
  subst hi
  exact not_le_of_gt (Finset.mem_filter.mp hlo).2 (Finset.mem_filter.mp hhi).2

/-- The upper ranked block is the complement of the lower ranked block inside
the ranked finite universe. -/
theorem upperRankFinset_eq_sdiff_lowerRankFinset
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    upperRankFinset s value hcard cut =
      s \ lowerRankFinset s value hcard cut := by
  classical
  ext a
  constructor
  · intro haupper
    refine Finset.mem_sdiff.mpr
      ⟨upperRankFinset_subset s value hcard cut haupper, ?_⟩
    intro halower
    exact lowerRankFinset_disjoint_upperRankFinset
      s value hcard cut a halower haupper
  · intro ha
    have has : a ∈ s := (Finset.mem_sdiff.mp ha).1
    have hanotlower : a ∉ lowerRankFinset s value hcard cut :=
      (Finset.mem_sdiff.mp ha).2
    have himage :
        a ∈ Finset.image (rankAgentByValue s value hcard)
          (Finset.univ : Finset (Fin k)) := by
      rw [image_rankAgentByValue_univ s value hcard]
      exact has
    rcases Finset.mem_image.mp himage with ⟨i, _hi, hi_eq⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hi_eq⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    by_contra hnot
    have hi_lt : i.val < cut := Nat.lt_of_not_ge hnot
    exact hanotlower (Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_lt⟩, hi_eq⟩)

theorem lowerRank_value_le_upperRank_value
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    ∀ high : α, high ∈ upperRankFinset s value hcard cut →
      ∀ low : α, low ∈ lowerRankFinset s value hcard cut →
        value low ≤ value high := by
  classical
  intro high hhigh low hlow
  rcases Finset.mem_image.mp hhigh with ⟨hi, hhi, rfl⟩
  rcases Finset.mem_image.mp hlow with ⟨lo, hlo, rfl⟩
  have hlo_lt_hi : lo.val < hi.val :=
    Nat.lt_of_lt_of_le (Finset.mem_filter.mp hlo).2
      (Finset.mem_filter.mp hhi).2
  have hmono :=
    rankValueByValue_mono s value hcard lo hi hlo_lt_hi
  rw [rankValueByValue_eq_value s value hcard lo] at hmono
  rw [rankValueByValue_eq_value s value hcard hi] at hmono
  exact hmono

theorem lowerRankFinset_card (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    (lowerRankFinset s value hcard cut).card = min k cut := by
  classical
  unfold lowerRankFinset
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  exact Fin.card_filter_val_lt (n := k) (m := cut)

theorem lowerRankFinset_card_add_upperRankFinset_card
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    (lowerRankFinset s value hcard cut).card +
      (upperRankFinset s value hcard cut).card = k := by
  classical
  unfold lowerRankFinset upperRankFinset
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  have hfilter :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k)))
      (p := fun i : Fin k => i.val < cut)
  simpa [Nat.not_lt] using hfilter

theorem upperRankFinset_card (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    (upperRankFinset s value hcard cut).card = k - min k cut := by
  classical
  have hsum :=
    lowerRankFinset_card_add_upperRankFinset_card s value hcard cut
  have hlow := lowerRankFinset_card s value hcard cut
  calc
    (upperRankFinset s value hcard cut).card
        = min k cut + (upperRankFinset s value hcard cut).card -
            min k cut := by
          rw [Nat.add_sub_cancel_left]
    _ = k - min k cut := by
          rw [← hlow, hsum]

theorem lowerRankFinset_card_half (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    (lowerRankFinset s value hcard (k / 2)).card = k / 2 := by
  rw [lowerRankFinset_card]
  exact min_eq_right (Nat.div_le_self k 2)

theorem upperRankFinset_card_half (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    (upperRankFinset s value hcard (k / 2)).card = k - k / 2 := by
  rw [upperRankFinset_card]
  exact congrArg (fun x => k - x) (min_eq_right (Nat.div_le_self k 2))

/--
Elements whose sorted rank index lies in the half-open interval `[lo, hi)`.
The interval is taken in the nondecreasing `(value, tie-breaker)` order.
-/
noncomputable def rankIntervalFinset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (lo hi : ℕ) : Finset α :=
  ((Finset.univ : Finset (Fin k)).filter fun i => lo ≤ i.val ∧ i.val < hi).image
    (rankAgentByValue s value hcard)

theorem rankIntervalFinset_subset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (lo hi : ℕ) :
    rankIntervalFinset s value hcard lo hi ⊆ s := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
  exact rankAgentByValue_mem s value hcard i

theorem rankIntervalFinset_card_le_width (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (lo hi : ℕ) :
    (rankIntervalFinset s value hcard lo hi).card ≤ hi - lo := by
  classical
  let I : Finset (Fin k) :=
    (Finset.univ : Finset (Fin k)).filter fun i => lo ≤ i.val ∧ i.val < hi
  unfold rankIntervalFinset
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  have hmaps : Set.MapsTo (fun i : Fin k => i.val) (I : Set (Fin k))
      (Finset.Ico lo hi : Set ℕ) := by
    intro i hiI
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hiI).2
  have hinj : Set.InjOn (fun i : Fin k => i.val) (I : Set (Fin k)) := by
    intro i _hi j _hj hval
    exact Fin.ext hval
  have hle := Finset.card_le_card_of_injOn (fun i : Fin k => i.val) hmaps hinj
  simpa [I, Nat.card_Ico] using hle

theorem rankIntervalFinset_card_eq_width_of_le
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) {lo hi : ℕ}
    (hhi : hi ≤ k) :
    (rankIntervalFinset s value hcard lo hi).card = hi - lo := by
  classical
  let I : Finset (Fin k) :=
    (Finset.univ : Finset (Fin k)).filter fun i => lo ≤ i.val ∧ i.val < hi
  let J : Finset ℕ := Finset.Ico lo hi
  have hmaps_to_J : Set.MapsTo (fun i : Fin k => i.val) (I : Set (Fin k)) (J : Set ℕ) := by
    intro i hiI
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hiI).2
  have hinj_to_J : Set.InjOn (fun i : Fin k => i.val) (I : Set (Fin k)) := by
    intro i _hi j _hj hval
    exact Fin.ext hval
  have hI_le_J : I.card ≤ J.card :=
    Finset.card_le_card_of_injOn (fun i : Fin k => i.val) hmaps_to_J hinj_to_J
  let toI : J → I := fun n =>
    let hn := Finset.mem_Ico.mp n.property
    ⟨⟨n.1, lt_of_lt_of_le hn.2 hhi⟩, by
      simp [I, hn.1, hn.2]⟩
  have hJ_le_I : J.card ≤ I.card := by
    refine Finset.card_le_card_of_injective (s := J) (t := I) (f := toI) ?_
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : I => ((x : Fin k).val)) hab
  have hI_card : I.card = J.card := le_antisymm hI_le_J hJ_le_I
  unfold rankIntervalFinset
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  simpa [I, J, Nat.card_Ico] using hI_card

theorem disjoint_rankIntervalFinset_of_le
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k)
    {lo₁ hi₁ lo₂ hi₂ : ℕ} (hsep : hi₁ ≤ lo₂) :
    Disjoint (rankIntervalFinset s value hcard lo₁ hi₁)
      (rankIntervalFinset s value hcard lo₂ hi₂) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha₁ ha₂
  rcases Finset.mem_image.mp ha₁ with ⟨i₁, hi₁mem, hi₁eq⟩
  rcases Finset.mem_image.mp ha₂ with ⟨i₂, hi₂mem, hi₂eq⟩
  have hagent :
      rankAgentByValue s value hcard i₁ =
        rankAgentByValue s value hcard i₂ := by
    rw [hi₁eq, hi₂eq]
  have hidx : i₁ = i₂ :=
    rankAgentByValue_injective s value hcard hagent
  subst i₂
  have hleft := (Finset.mem_filter.mp hi₁mem).2
  have hright := (Finset.mem_filter.mp hi₂mem).2
  exact not_lt_of_ge (hsep.trans hright.1) hleft.2

theorem rankInterval_value_le_rankInterval
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k)
    {lo₁ hi₁ lo₂ hi₂ : ℕ} (hsep : hi₁ ≤ lo₂) :
    ∀ high : α, high ∈ rankIntervalFinset s value hcard lo₂ hi₂ →
      ∀ low : α, low ∈ rankIntervalFinset s value hcard lo₁ hi₁ →
        value low ≤ value high := by
  classical
  intro high hhigh low hlow
  rcases Finset.mem_image.mp hhigh with ⟨ihi, hihi, rfl⟩
  rcases Finset.mem_image.mp hlow with ⟨ilo, hilo, rfl⟩
  have hilo_bounds := (Finset.mem_filter.mp hilo).2
  have hihi_bounds := (Finset.mem_filter.mp hihi).2
  have hlt : ilo.val < ihi.val :=
    Nat.lt_of_lt_of_le hilo_bounds.2 (hsep.trans hihi_bounds.1)
  have hmono := rankValueByValue_mono s value hcard ilo ihi hlt
  rw [rankValueByValue_eq_value s value hcard ilo] at hmono
  rw [rankValueByValue_eq_value s value hcard ihi] at hmono
  exact hmono

/--
Descending fixed-width rank block.  Block `0` is the top `width` elements,
block `1` is the next `width` elements, and later blocks continue downward in
the sorted order.  Saturating natural subtraction makes high block numbers
empty.
-/
noncomputable def descendingRankBlockFinset (s : Finset α) (value : α → ℝ)
    (width block : ℕ) : Finset α :=
  rankIntervalFinset s value rfl
    (s.card - (block + 1) * width)
    (s.card - block * width)

theorem nat_lt_succ_div_mul_self {q width : ℕ} (hwidth : 0 < width) :
    q < (q / width + 1) * width := by
  calc
    q = width * (q / width) + q % width := by
      exact (Nat.div_add_mod q width).symm
    _ < width * (q / width) + width := by
      exact Nat.add_lt_add_left (Nat.mod_lt q hwidth) _
    _ = (q / width + 1) * width := by
      rw [Nat.add_mul, one_mul, Nat.mul_comm (q / width) width]

theorem descendingRankBlockFinset_subset (s : Finset α) (value : α → ℝ)
    (width block : ℕ) :
    descendingRankBlockFinset s value width block ⊆ s := by
  classical
  exact rankIntervalFinset_subset s value rfl
    (s.card - (block + 1) * width)
    (s.card - block * width)

theorem descendingRankBlockFinset_card_le_width
    (s : Finset α) (value : α → ℝ) (width block : ℕ) :
    (descendingRankBlockFinset s value width block).card ≤ width := by
  classical
  have hwidth :=
    rankIntervalFinset_card_le_width s value rfl
      (s.card - (block + 1) * width)
      (s.card - block * width)
  have hblock_width :
      (s.card - block * width) - (s.card - (block + 1) * width) ≤ width := by
    have hmul : (block + 1) * width = block * width + width := by
      rw [Nat.add_mul, one_mul]
    rw [hmul]
    rw [Nat.sub_le_iff_le_add]
    omega
  exact hwidth.trans hblock_width

theorem descendingRankBlockFinset_card_eq_width_of_le
    (s : Finset α) (value : α → ℝ) {width block : ℕ}
    (hblock : (block + 1) * width ≤ s.card) :
    (descendingRankBlockFinset s value width block).card = width := by
  classical
  have hcard :=
    rankIntervalFinset_card_eq_width_of_le s value rfl
      (lo := s.card - (block + 1) * width)
      (hi := s.card - block * width)
      (Nat.sub_le _ _)
  have hwidth :
      (s.card - block * width) - (s.card - (block + 1) * width) = width := by
    have hmul : (block + 1) * width = block * width + width := by
      rw [Nat.add_mul, one_mul]
    rw [hmul] at hblock ⊢
    omega
  simpa [descendingRankBlockFinset, hwidth] using hcard

theorem exists_mem_descendingRankBlockFinset
    (s : Finset α) (value : α → ℝ) {width : ℕ} (hwidth : 0 < width)
    {a : α} (ha : a ∈ s) :
    ∃ block : ℕ, a ∈ descendingRankBlockFinset s value width block := by
  classical
  have ha_image :
      a ∈ Finset.image (rankAgentByValue s value rfl)
        (Finset.univ : Finset (Fin s.card)) := by
    simpa [image_rankAgentByValue_univ s value rfl] using ha
  rcases Finset.mem_image.mp ha_image with ⟨i, hi, rfl⟩
  let q := s.card - 1 - i.val
  let block := q / width
  refine ⟨block, ?_⟩
  unfold descendingRankBlockFinset rankIntervalFinset
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
  have hq_lt : q < (block + 1) * width := by
    simpa [block] using nat_lt_succ_div_mul_self (q := q) hwidth
  have hblock_mul_le : block * width ≤ q := by
    simpa [block, Nat.mul_comm] using Nat.div_mul_le_self q width
  constructor
  · omega
  · omega

theorem exists_mem_descendingRankBlockFinset_lt_card
    (s : Finset α) (value : α → ℝ) {width : ℕ} (hwidth : 0 < width)
    {a : α} (ha : a ∈ s) :
    ∃ block : ℕ, block < s.card ∧
      a ∈ descendingRankBlockFinset s value width block := by
  classical
  have ha_image :
      a ∈ Finset.image (rankAgentByValue s value rfl)
        (Finset.univ : Finset (Fin s.card)) := by
    simpa [image_rankAgentByValue_univ s value rfl] using ha
  rcases Finset.mem_image.mp ha_image with ⟨i, hi, rfl⟩
  let q := s.card - 1 - i.val
  let block := q / width
  have hq_lt_card : q < s.card := by
    omega
  have hblock_lt_card : block < s.card := by
    exact (Nat.div_le_self q width).trans_lt hq_lt_card
  refine ⟨block, hblock_lt_card, ?_⟩
  unfold descendingRankBlockFinset rankIntervalFinset
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
  have hq_lt : q < (block + 1) * width := by
    simpa [block] using nat_lt_succ_div_mul_self (q := q) hwidth
  have hblock_mul_le : block * width ≤ q := by
    simpa [block, Nat.mul_comm] using Nat.div_mul_le_self q width
  constructor
  · omega
  · omega

theorem disjoint_descendingRankBlockFinset_of_lt
    (s : Finset α) (value : α → ℝ) (width : ℕ) {lower higher : ℕ}
    (hblock : higher < lower) :
    Disjoint (descendingRankBlockFinset s value width lower)
      (descendingRankBlockFinset s value width higher) := by
  classical
  have hsep :
      s.card - lower * width ≤ s.card - (higher + 1) * width := by
    exact Nat.sub_le_sub_left
      (Nat.mul_le_mul_right width (Nat.succ_le_of_lt hblock)) s.card
  simpa [descendingRankBlockFinset] using
    disjoint_rankIntervalFinset_of_le
      (s := s) (value := value) (hcard := rfl)
      (lo₁ := s.card - (lower + 1) * width)
      (hi₁ := s.card - lower * width)
      (lo₂ := s.card - (higher + 1) * width)
      (hi₂ := s.card - higher * width)
      hsep

theorem next_descendingRankBlock_value_le_current
    (s : Finset α) (value : α → ℝ) (width block : ℕ) :
    ∀ high : α, high ∈ descendingRankBlockFinset s value width block →
      ∀ low : α, low ∈ descendingRankBlockFinset s value width (block + 1) →
        value low ≤ value high := by
  classical
  simpa [descendingRankBlockFinset, Nat.add_assoc] using
    rankInterval_value_le_rankInterval
      (s := s) (value := value) (hcard := rfl)
      (lo₁ := s.card - (block + 2) * width)
      (hi₁ := s.card - (block + 1) * width)
      (lo₂ := s.card - (block + 1) * width)
      (hi₂ := s.card - block * width)
      (le_rfl)

/--
The `take` largest elements of `s` by `value`, with deterministic tie-breaking
inherited from `rankAgentByValue`.  If `take` exceeds `s.card`, this returns
all of `s`.
-/
noncomputable def topRankFinset (s : Finset α) (value : α → ℝ)
    (take : ℕ) : Finset α :=
  upperRankFinset s value rfl (s.card - take)

theorem topRankFinset_subset (s : Finset α) (value : α → ℝ)
    (take : ℕ) :
    topRankFinset s value take ⊆ s := by
  classical
  exact upperRankFinset_subset s value rfl (s.card - take)

theorem descendingRankBlockFinset_zero_eq_topRankFinset
    (s : Finset α) (value : α → ℝ) (take : ℕ) :
    descendingRankBlockFinset s value take 0 = topRankFinset s value take := by
  classical
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    have hidx := (Finset.mem_filter.mp hi).2
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simpa using hidx.1⟩
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    have hidx := (Finset.mem_filter.mp hi).2
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    exact ⟨by simpa using hidx, by simp⟩

theorem topRankFinset_card (s : Finset α) (value : α → ℝ)
    (take : ℕ) :
    (topRankFinset s value take).card =
      s.card - min s.card (s.card - take) := by
  classical
  exact upperRankFinset_card s value rfl (s.card - take)

theorem topRankFinset_card_le (s : Finset α) (value : α → ℝ)
    (take : ℕ) :
    (topRankFinset s value take).card ≤ take := by
  classical
  rw [topRankFinset_card]
  rw [min_eq_right (Nat.sub_le s.card take)]
  omega

theorem topRankFinset_card_eq_of_le (s : Finset α) (value : α → ℝ)
    {take : ℕ} (htake : take ≤ s.card) :
    (topRankFinset s value take).card = take := by
  classical
  rw [topRankFinset_card]
  rw [min_eq_right (Nat.sub_le s.card take)]
  omega

theorem sdiff_topRankFinset_eq_lowerRankFinset
    (s : Finset α) (value : α → ℝ) (take : ℕ) :
    s \ topRankFinset s value take =
      lowerRankFinset s value rfl (s.card - take) := by
  classical
  let cut := s.card - take
  have hupper :
      upperRankFinset s value rfl cut =
        s \ lowerRankFinset s value rfl cut :=
    upperRankFinset_eq_sdiff_lowerRankFinset s value rfl cut
  ext a
  constructor
  · intro ha
    have has : a ∈ s := (Finset.mem_sdiff.mp ha).1
    have hnotupper : a ∉ topRankFinset s value take :=
      (Finset.mem_sdiff.mp ha).2
    by_contra hnotlower
    have haupper : a ∈ upperRankFinset s value rfl cut := by
      rw [hupper]
      exact Finset.mem_sdiff.mpr ⟨has, hnotlower⟩
    exact hnotupper (by simpa [topRankFinset, cut] using haupper)
  · intro hlow
    refine Finset.mem_sdiff.mpr ⟨lowerRankFinset_subset s value rfl cut hlow, ?_⟩
    intro htop
    exact lowerRankFinset_disjoint_upperRankFinset
      s value rfl cut a hlow (by simpa [topRankFinset, cut] using htop)

theorem outside_topRank_value_le_inside_topRank_value
    (s : Finset α) (value : α → ℝ) (take : ℕ) :
    ∀ high : α, high ∈ topRankFinset s value take →
      ∀ low : α, low ∈ s \ topRankFinset s value take →
        value low ≤ value high := by
  classical
  intro high hhigh low hlow
  let cut := s.card - take
  have hhigh_upper : high ∈ upperRankFinset s value rfl cut := by
    simpa [topRankFinset, cut] using hhigh
  have hlow_lower : low ∈ lowerRankFinset s value rfl cut := by
    simpa [sdiff_topRankFinset_eq_lowerRankFinset, cut] using hlow
  exact lowerRank_value_le_upperRank_value
    s value rfl cut high hhigh_upper low hlow_lower

end FiniteRanking
end AppliedModelingLib
