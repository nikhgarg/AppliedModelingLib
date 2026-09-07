import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

open scoped BigOperators

namespace AppliedModelingLib
namespace SimplexRounding

private noncomputable def floorCount {α : Type*} (Q : ℕ) (ν : α → ℝ) (a : α) : ℕ :=
  Nat.floor ((Q : ℝ) * ν a)

private theorem floorCount_sum_le
    {α : Type*} [Fintype α]
    {Q : ℕ} (ν : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1) :
    (∑ a : α, floorCount Q ν a) ≤ Q := by
  have hfloor_le :
      ∀ a : α, ((floorCount Q ν a : ℕ) : ℝ) ≤ (Q : ℝ) * ν a := by
    intro a
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (hν_nonneg a))
  have hcast_le : ((∑ a : α, floorCount Q ν a : ℕ) : ℝ) ≤ (Q : ℝ) := by
    calc
      ((∑ a : α, floorCount Q ν a : ℕ) : ℝ)
          = ∑ a : α, ((floorCount Q ν a : ℕ) : ℝ) := by
              simp
      _ ≤ ∑ a : α, (Q : ℝ) * ν a := by
              exact Finset.sum_le_sum (by
                intro a _ha
                exact hfloor_le a)
      _ = (Q : ℝ) := by
              rw [← Finset.mul_sum, hν_sum, mul_one]
  exact_mod_cast hcast_le

private theorem floorCount_div_close
    {Q : ℕ} (hQ : 0 < Q) {x : ℝ} (hx : 0 ≤ x) :
    |(((Nat.floor ((Q : ℝ) * x) : ℝ) / (Q : ℝ)) - x)| < 1 / (Q : ℝ) := by
  let n : ℕ := Nat.floor ((Q : ℝ) * x)
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hfloor_le : (n : ℝ) ≤ (Q : ℝ) * x := by
    dsimp [n]
    exact Nat.floor_le (mul_nonneg hQpos.le hx)
  have hfloor_div_le : (n : ℝ) / (Q : ℝ) ≤ x := by
    rw [div_le_iff₀ hQpos]
    simpa [mul_comm] using hfloor_le
  have hscaled_lt : (Q : ℝ) * x < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one ((Q : ℝ) * x)
  have hx_lt : x < ((n : ℝ) + 1) / (Q : ℝ) := by
    rw [lt_div_iff₀ hQpos]
    simpa [mul_comm] using hscaled_lt
  have hright : (n : ℝ) / (Q : ℝ) - x < 1 / (Q : ℝ) := by
    have hnonpos : (n : ℝ) / (Q : ℝ) - x ≤ 0 := by linarith
    have hone_pos : 0 < 1 / (Q : ℝ) := by positivity
    linarith
  have hleft : -(1 / (Q : ℝ)) < (n : ℝ) / (Q : ℝ) - x := by
    have hx_lt_add : x < (n : ℝ) / (Q : ℝ) + 1 / (Q : ℝ) := by
      calc
        x < ((n : ℝ) + 1) / (Q : ℝ) := hx_lt
        _ = (n : ℝ) / (Q : ℝ) + 1 / (Q : ℝ) := by ring
    linarith
  simpa [n] using abs_lt.mpr ⟨hleft, hright⟩

private theorem floorCount_div_nonpos_sub
    {Q : ℕ} (hQ : 0 < Q) {x : ℝ} (hx : 0 ≤ x) :
    (Nat.floor ((Q : ℝ) * x) : ℝ) / (Q : ℝ) - x ≤ 0 := by
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hfloor_le :
      (Nat.floor ((Q : ℝ) * x) : ℝ) ≤ (Q : ℝ) * x := by
    exact Nat.floor_le (mul_nonneg hQpos.le hx)
  have hfloor_div_le :
      (Nat.floor ((Q : ℝ) * x) : ℝ) / (Q : ℝ) ≤ x := by
    rw [div_le_iff₀ hQpos]
    simpa [mul_comm] using hfloor_le
  linarith

private theorem simplex_remainder_coordinate_close
    {α : Type*} [Fintype α] [DecidableEq α]
    {Q : ℕ} (ν : α → ℝ) (a₀ : α)
    (hQ : 0 < Q)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1) :
    abs ((((Q - (∑ a ∈ (Finset.univ.erase a₀), floorCount Q ν a)) : ℕ) : ℝ) /
        (Q : ℝ) - ν a₀)
      ≤ ((Finset.univ.erase a₀).card : ℝ) / (Q : ℝ) := by
  let s : Finset α := Finset.univ.erase a₀
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hsum_floor_le : (∑ a ∈ s, floorCount Q ν a) ≤ Q := by
    refine le_trans ?_ (floorCount_sum_le (Q := Q) ν hν_nonneg hν_sum)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro a ha
        exact Finset.mem_univ a)
      (by
        intro a _ha _hnot
        exact Nat.zero_le _)
  have hsub_cast :
      (((Q - (∑ a ∈ s, floorCount Q ν a)) : ℕ) : ℝ) =
        (Q : ℝ) - ∑ a ∈ s, ((floorCount Q ν a : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsum_floor_le]
    congr 1
    simp
  have hν_sum_erase : ∑ a ∈ s, ν a + ν a₀ = 1 := by
    calc
      ∑ a ∈ s, ν a + ν a₀ = ∑ a : α, ν a := by
        exact Finset.sum_erase_add (Finset.univ : Finset α) ν (Finset.mem_univ a₀)
      _ = 1 := hν_sum
  have hdiff_eq :
      (((Q - (∑ a ∈ s, floorCount Q ν a)) : ℕ) : ℝ) / (Q : ℝ) - ν a₀
        = ∑ a ∈ s, (ν a - ((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ)) := by
    calc
      (((Q - (∑ a ∈ s, floorCount Q ν a)) : ℕ) : ℝ) / (Q : ℝ) - ν a₀
          = ((Q : ℝ) - ∑ a ∈ s, ((floorCount Q ν a : ℕ) : ℝ)) /
              (Q : ℝ) - ν a₀ := by
                rw [hsub_cast]
      _ = 1 - (∑ a ∈ s, ((floorCount Q ν a : ℕ) : ℝ)) / (Q : ℝ) - ν a₀ := by
                field_simp [ne_of_gt hQpos]
      _ = ∑ a ∈ s, ν a -
            (∑ a ∈ s, ((floorCount Q ν a : ℕ) : ℝ)) / (Q : ℝ) := by
                linarith
      _ = ∑ a ∈ s, (ν a - ((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ)) := by
                rw [Finset.sum_sub_distrib]
                congr 1
                rw [Finset.sum_div]
  have hterm_nonneg :
      ∀ a ∈ s, 0 ≤ ν a - ((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ) := by
    intro a _ha
    have hsub :=
      floorCount_div_nonpos_sub (Q := Q) hQ (x := ν a) (hν_nonneg a)
    dsimp [floorCount] at hsub ⊢
    linarith
  have habs_eq :
      abs ((((Q - (∑ a ∈ s, floorCount Q ν a)) : ℕ) : ℝ) /
          (Q : ℝ) - ν a₀)
        = ∑ a ∈ s, (ν a - ((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ)) := by
    rw [hdiff_eq]
    exact abs_of_nonneg (Finset.sum_nonneg hterm_nonneg)
  rw [habs_eq]
  have hterm_le :
      ∀ a ∈ s, ν a - ((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ) ≤
        1 / (Q : ℝ) := by
    intro a _ha
    have hclose := floorCount_div_close (Q := Q) hQ (x := ν a) (hν_nonneg a)
    dsimp [floorCount] at hclose ⊢
    have hright := (abs_lt.mp hclose).1
    linarith
  calc
    ∑ a ∈ s, (ν a - ((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ))
        ≤ ∑ a ∈ s, (1 / (Q : ℝ)) := by
            exact Finset.sum_le_sum hterm_le
    _ = ((s.card : ℕ) : ℝ) / (Q : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring

/--
For every sufficiently large denominator `Q`, a finite simplex point has an
integer count vector summing to `Q` whose empirical frequencies are uniformly
within `ε`.

The construction floors every coordinate, then puts the remaining mass on one
fixed coordinate. The resulting reusable bound is `Fintype.card α / Q`.
-/
theorem exists_countVector_close_to_simplex_of_large_denominator
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ν : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    {Q : ℕ} (hQ : 0 < Q)
    {ε : ℝ} (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      ∀ a : α, |((q a : ℝ) / Q) - ν a| < ε := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  let baseSum : ℕ := ∑ a : α, floorCount Q ν a
  let rem : ℕ := Q - baseSum
  let q : α → ℕ := fun a => floorCount Q ν a + if a = a₀ then rem else 0
  have hbase_le : baseSum ≤ Q := by
    dsimp [baseSum]
    exact floorCount_sum_le (Q := Q) ν hν_nonneg hν_sum
  have hq_sum : ∑ a : α, q a = Q := by
    calc
      ∑ a : α, q a
          = ∑ a : α, (floorCount Q ν a + if a = a₀ then rem else 0) := rfl
      _ = baseSum + rem := by
              dsimp [baseSum]
              rw [Finset.sum_add_distrib]
              congr 1
              exact Fintype.sum_ite_eq' a₀ (fun _a : α => rem)
      _ = Q := by
              dsimp [rem]
              omega
  refine ⟨q, hq_sum, ?_⟩
  intro a
  by_cases ha : a = a₀
  · subst a
    have hq_a₀ :
        q a₀ = Q - (∑ a ∈ (Finset.univ.erase a₀), floorCount Q ν a) := by
      have hsum_split :
          baseSum = ∑ a ∈ (Finset.univ.erase a₀), floorCount Q ν a +
            floorCount Q ν a₀ := by
        dsimp [baseSum]
        exact (Finset.sum_erase_add (Finset.univ : Finset α)
          (fun a : α => floorCount Q ν a) (Finset.mem_univ a₀)).symm
      simp [q, rem]
      omega
    have hclose :=
      simplex_remainder_coordinate_close (Q := Q) ν a₀ hQ hν_nonneg hν_sum
    calc
      |((q a₀ : ℝ) / (Q : ℝ)) - ν a₀|
          = abs ((((Q - (∑ a ∈ (Finset.univ.erase a₀), floorCount Q ν a)) : ℕ) : ℝ) /
              (Q : ℝ) - ν a₀) := by
                rw [hq_a₀]
      _ ≤ ((Finset.univ.erase a₀).card : ℝ) / (Q : ℝ) := hclose
      _ ≤ (Fintype.card α : ℝ) / (Q : ℝ) := by
              have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
              gcongr
              exact_mod_cast Finset.card_le_univ (Finset.univ.erase a₀)
      _ < ε := hQ_large
  · have hq_a : q a = floorCount Q ν a := by
      dsimp [q]
      simp [ha]
    have hclose := floorCount_div_close (Q := Q) hQ (x := ν a) (hν_nonneg a)
    have hone_le_card : (1 : ℝ) ≤ Fintype.card α := by
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ‹Nonempty α›))
    have hone_div_le_card_div : 1 / (Q : ℝ) ≤ (Fintype.card α : ℝ) / (Q : ℝ) := by
      have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
      gcongr
    calc
      |((q a : ℝ) / (Q : ℝ)) - ν a|
          = |(((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ)) - ν a| := by
              rw [hq_a]
      _ < 1 / (Q : ℝ) := hclose
      _ ≤ (Fintype.card α : ℝ) / (Q : ℝ) := hone_div_le_card_div
      _ < ε := hQ_large

/--
Anchored finite-simplex rounding.  This is the same floor-plus-remainder
construction as `exists_countVector_close_to_simplex_of_large_denominator`,
but the leftover mass is placed on the caller-specified anchor.  Consequently,
every non-anchor coordinate with nonzero count has positive simplex mass.
-/
theorem exists_countVector_close_to_simplex_of_large_denominator_with_anchor
    {α : Type*} [Fintype α] [DecidableEq α]
    (ν : α → ℝ) (a₀ : α)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    {Q : ℕ} (hQ : 0 < Q)
    {ε : ℝ} (hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < ε) :
    ∃ q : α → ℕ,
      (∑ a : α, q a = Q) ∧
      (∀ a : α, |((q a : ℝ) / Q) - ν a| < ε) ∧
      ∀ a : α, q a ≠ 0 → a = a₀ ∨ 0 < ν a := by
  classical
  let baseSum : ℕ := ∑ a : α, floorCount Q ν a
  let rem : ℕ := Q - baseSum
  let q : α → ℕ := fun a => floorCount Q ν a + if a = a₀ then rem else 0
  have hbase_le : baseSum ≤ Q := by
    dsimp [baseSum]
    exact floorCount_sum_le (Q := Q) ν hν_nonneg hν_sum
  have hq_sum : ∑ a : α, q a = Q := by
    calc
      ∑ a : α, q a
          = ∑ a : α, (floorCount Q ν a + if a = a₀ then rem else 0) := rfl
      _ = baseSum + rem := by
              dsimp [baseSum]
              rw [Finset.sum_add_distrib]
              congr 1
              exact Fintype.sum_ite_eq' a₀ (fun _a : α => rem)
      _ = Q := by
              dsimp [rem]
              omega
  refine ⟨q, hq_sum, ?_, ?_⟩
  · intro a
    by_cases ha : a = a₀
    · subst a
      have hq_a₀ :
          q a₀ = Q - (∑ a ∈ (Finset.univ.erase a₀), floorCount Q ν a) := by
        have hsum_split :
            baseSum = ∑ a ∈ (Finset.univ.erase a₀), floorCount Q ν a +
              floorCount Q ν a₀ := by
          dsimp [baseSum]
          exact (Finset.sum_erase_add (Finset.univ : Finset α)
            (fun a : α => floorCount Q ν a) (Finset.mem_univ a₀)).symm
        simp [q, rem]
        omega
      have hclose :=
        simplex_remainder_coordinate_close (Q := Q) ν a₀ hQ hν_nonneg hν_sum
      calc
        |((q a₀ : ℝ) / (Q : ℝ)) - ν a₀|
            = abs ((((Q - (∑ a ∈ (Finset.univ.erase a₀), floorCount Q ν a)) : ℕ) : ℝ) /
                (Q : ℝ) - ν a₀) := by
                  rw [hq_a₀]
        _ ≤ ((Finset.univ.erase a₀).card : ℝ) / (Q : ℝ) := hclose
        _ ≤ (Fintype.card α : ℝ) / (Q : ℝ) := by
                have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
                gcongr
                exact_mod_cast Finset.card_le_univ (Finset.univ.erase a₀)
        _ < ε := hQ_large
    · have hq_a : q a = floorCount Q ν a := by
        dsimp [q]
        simp [ha]
      have hclose := floorCount_div_close (Q := Q) hQ (x := ν a) (hν_nonneg a)
      have hone_le_card : (1 : ℝ) ≤ Fintype.card α := by
        exact_mod_cast
          (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨a₀⟩))
      have hone_div_le_card_div :
          1 / (Q : ℝ) ≤ (Fintype.card α : ℝ) / (Q : ℝ) := by
        have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
        gcongr
      calc
        |((q a : ℝ) / (Q : ℝ)) - ν a|
            = |(((floorCount Q ν a : ℕ) : ℝ) / (Q : ℝ)) - ν a| := by
                rw [hq_a]
        _ < 1 / (Q : ℝ) := hclose
        _ ≤ (Fintype.card α : ℝ) / (Q : ℝ) := hone_div_le_card_div
        _ < ε := hQ_large
  · intro a hqa
    by_cases ha : a = a₀
    · exact Or.inl ha
    · have hq_a : q a = floorCount Q ν a := by
        dsimp [q]
        simp [ha]
      have hfloor_ne : floorCount Q ν a ≠ 0 := by
        simpa [hq_a] using hqa
      have hfloor_pos_real : 0 < ((floorCount Q ν a : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hfloor_ne
      have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
      have hfloor_le :
          ((floorCount Q ν a : ℕ) : ℝ) ≤ (Q : ℝ) * ν a := by
        exact Nat.floor_le (mul_nonneg hQpos.le (hν_nonneg a))
      have hmul_pos : 0 < (Q : ℝ) * ν a :=
        lt_of_lt_of_le hfloor_pos_real hfloor_le
      exact Or.inr (by nlinarith)

/--
Finite-simplex count-vector approximation with an existential denominator.
-/
theorem exists_countVector_close_to_simplex
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ν : α → ℝ)
    (hν_nonneg : ∀ a, 0 ≤ ν a)
    (hν_sum : ∑ a : α, ν a = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : ℕ) (q : α → ℕ),
      0 < Q ∧
      (∑ a : α, q a = Q) ∧
      ∀ a : α, |((q a : ℝ) / Q) - ν a| < ε := by
  classical
  obtain ⟨Q, hQ_large_raw⟩ := exists_nat_gt ((Fintype.card α : ℝ) / ε)
  have hcard_div_nonneg : 0 ≤ (Fintype.card α : ℝ) / ε := by
    positivity
  have hQpos_real : 0 < (Q : ℝ) := lt_of_le_of_lt hcard_div_nonneg hQ_large_raw
  have hQ : 0 < Q := by exact_mod_cast hQpos_real
  have hQ_large : (Fintype.card α : ℝ) / (Q : ℝ) < ε := by
    have hcard_lt_mul : (Fintype.card α : ℝ) < (Q : ℝ) * ε := by
      calc
        (Fintype.card α : ℝ) = ((Fintype.card α : ℝ) / ε) * ε := by
          field_simp [ne_of_gt hε]
        _ < (Q : ℝ) * ε := by
          exact mul_lt_mul_of_pos_right hQ_large_raw hε
    rw [div_lt_iff₀ hQpos_real]
    simpa [mul_comm] using hcard_lt_mul
  obtain ⟨q, hq_sum, hq_close⟩ :=
    exists_countVector_close_to_simplex_of_large_denominator
      (α := α) ν hν_nonneg hν_sum hQ hQ_large
  exact ⟨Q, q, hQ, hq_sum, hq_close⟩

end SimplexRounding
end AppliedModelingLib
