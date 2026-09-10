import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators

namespace AppliedModelingLib
namespace FiniteRounding

/--
No coordinate can be simultaneously too high above an integer anchor while
another coordinate is too low below its anchor.

This is the discrete crossing condition used in rounding arguments for
separable finite optimization problems.
-/
def NoRoundingCrossing {κ : Type*} (a b : κ → ℕ) : Prop :=
  ∀ high low, ¬ (b high + 1 ≤ a high ∧ a low + 1 ≤ b low)

/--
Two-anchor version of `NoRoundingCrossing`.

`upper` is the integer threshold above which a coordinate is too high, while
`lower` is the integer threshold below which a coordinate is too low. This is
the shape used by rounding proofs around real optima, where upper and lower
integer anchors are naturally `ceil` and `floor` bounds.
-/
def NoRoundingCrossingBetween {κ : Type*}
    (a lower upper : κ → ℕ) : Prop :=
  ∀ high low, ¬ (upper high + 1 ≤ a high ∧ a low + 1 ≤ lower low)

namespace NoRoundingCrossing

theorem exists_low_of_high
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B C : ℕ} (high : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hNlt : N < B + C)
    (hhigh : b high + C ≤ a high) :
    ∃ low, a low < b low := by
  classical
  by_contra hnone
  have hall : ∀ i, b i ≤ a i := by
    intro i
    exact le_of_not_gt (by
      intro hlt
      exact hnone ⟨i, hlt⟩)
  let raised : κ → ℕ := fun i => if i = high then b high + C else b i
  have hraised_le : ∀ i, raised i ≤ a i := by
    intro i
    by_cases hi : i = high
    · subst hi
      simp [raised, hhigh]
    · simp [raised, hi, hall i]
  have hsum_raised_le : (∑ i : κ, raised i) ≤ ∑ i : κ, a i :=
    Finset.sum_le_sum (by
      intro i _hi
      exact hraised_le i)
  have hsum_raised : (∑ i : κ, raised i) = B + C := by
    have hpoint :
        (fun i : κ => raised i) =
          fun i : κ => b i + if i = high then C else 0 := by
      funext i
      by_cases hi : i = high
      · subst hi
        simp [raised]
      · simp [raised, hi]
    calc
      (∑ i : κ, raised i)
          = ∑ i : κ, (b i + if i = high then C else 0) := by
              rw [hpoint]
      _ = (∑ i : κ, b i) +
            ∑ i : κ, (if i = high then C else 0) := by
              rw [Finset.sum_add_distrib]
      _ = B + C := by
              rw [hb]
              congr 1
              exact Fintype.sum_ite_eq' high (fun _i : κ => C)
  have hB_add_C_le_N : B + C ≤ N := by
    rw [← ha, ← hsum_raised]
    exact hsum_raised_le
  exact (not_lt_of_ge hB_add_C_le_N) hNlt

theorem exists_high_of_low
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B C : ℕ} (low : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hBle : B ≤ N) (hCpos : 0 < C)
    (hlow : a low + C ≤ b low) :
    ∃ high, b high < a high := by
  classical
  by_contra hnone
  have hall : ∀ i, a i ≤ b i := by
    intro i
    exact le_of_not_gt (by
      intro hlt
      exact hnone ⟨i, hlt⟩)
  let raised : κ → ℕ := fun i => if i = low then a low + C else a i
  have hraised_le : ∀ i, raised i ≤ b i := by
    intro i
    by_cases hi : i = low
    · subst hi
      simp [raised, hlow]
    · simp [raised, hi, hall i]
  have hsum_raised_le : (∑ i : κ, raised i) ≤ ∑ i : κ, b i :=
    Finset.sum_le_sum (by
      intro i _hi
      exact hraised_le i)
  have hsum_raised : (∑ i : κ, raised i) = N + C := by
    have hpoint :
        (fun i : κ => raised i) =
          fun i : κ => a i + if i = low then C else 0 := by
      funext i
      by_cases hi : i = low
      · subst hi
        simp [raised]
      · simp [raised, hi]
    calc
      (∑ i : κ, raised i)
          = ∑ i : κ, (a i + if i = low then C else 0) := by
              rw [hpoint]
      _ = (∑ i : κ, a i) +
            ∑ i : κ, (if i = low then C else 0) := by
              rw [Finset.sum_add_distrib]
      _ = N + C := by
              rw [ha]
              congr 1
              exact Fintype.sum_ite_eq' low (fun _i : κ => C)
  have hN_add_C_le_N : N + C ≤ N := by
    calc
      N + C = ∑ i : κ, raised i := hsum_raised.symm
      _ ≤ ∑ i : κ, b i := hsum_raised_le
      _ = B := hb
      _ ≤ N := hBle
  exact (not_lt_of_ge hN_add_C_le_N) (Nat.lt_add_of_pos_right hCpos)

/--
If the integer allocation has no high/low crossing around anchors `b`, then no
coordinate is above its anchor by as much as the number of coordinates.
-/
theorem count_lt_anchor_add_card
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B : ℕ} (t : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hNlt : N < B + Fintype.card κ)
    (hno : NoRoundingCrossing a b) :
    a t < b t + Fintype.card κ := by
  by_contra hnot
  have hhigh : b t + Fintype.card κ ≤ a t := le_of_not_gt hnot
  obtain ⟨low, hlow_lt⟩ :=
    exists_low_of_high a b t ha hb hNlt hhigh
  have hcard_pos : 0 < Fintype.card κ :=
    Fintype.card_pos_iff.mpr ⟨t⟩
  have hhigh_one : b t + 1 ≤ a t :=
    le_trans
      (Nat.add_le_add_left (Nat.succ_le_of_lt hcard_pos) (b t))
      hhigh
  have hlow_one : a low + 1 ≤ b low :=
    Nat.succ_le_of_lt hlow_lt
  exact hno t low ⟨hhigh_one, hlow_one⟩

/--
If the integer allocation has no high/low crossing around anchors `b`, then no
coordinate is below its anchor by as much as the number of coordinates.
-/
theorem anchor_lt_count_add_card
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B : ℕ} (t : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hBle : B ≤ N)
    (hno : NoRoundingCrossing a b) :
    b t < a t + Fintype.card κ := by
  by_contra hnot
  have hlow : a t + Fintype.card κ ≤ b t := le_of_not_gt hnot
  have hcard_pos : 0 < Fintype.card κ :=
    Fintype.card_pos_iff.mpr ⟨t⟩
  obtain ⟨high, hhigh_lt⟩ :=
    exists_high_of_low a b t ha hb hBle hcard_pos hlow
  have hhigh_one : b high + 1 ≤ a high :=
    Nat.succ_le_of_lt hhigh_lt
  have hlow_one : a t + 1 ≤ b t :=
    le_trans
      (Nat.add_le_add_left (Nat.succ_le_of_lt hcard_pos) (a t))
      hlow
  exact hno high t ⟨hhigh_one, hlow_one⟩

end NoRoundingCrossing

namespace NoRoundingCrossingBetween

theorem exists_low_of_high
    {κ : Type*} [Fintype κ]
    (a lower upper : κ → ℕ) {N L C : ℕ} (high : κ)
    (ha : (∑ i : κ, a i) = N)
    (hlower : (∑ i : κ, lower i) = L)
    (hNlt : N < L + C)
    (horder : ∀ i, lower i ≤ upper i)
    (hhigh : upper high + C ≤ a high) :
    ∃ low, a low < lower low := by
  classical
  by_contra hnone
  have hall : ∀ i, lower i ≤ a i := by
    intro i
    exact le_of_not_gt (by
      intro hlt
      exact hnone ⟨i, hlt⟩)
  let raised : κ → ℕ := fun i => if i = high then lower high + C else lower i
  have hraised_le : ∀ i, raised i ≤ a i := by
    intro i
    by_cases hi : i = high
    · have hlower_upper : lower i + C ≤ upper i + C :=
        Nat.add_le_add_right (horder i) C
      have hhigh_i : upper i + C ≤ a i := by
        simpa [hi] using hhigh
      simpa [raised, hi] using le_trans hlower_upper hhigh_i
    · simp [raised, hi, hall i]
  have hsum_raised_le : (∑ i : κ, raised i) ≤ ∑ i : κ, a i :=
    Finset.sum_le_sum (by
      intro i _hi
      exact hraised_le i)
  have hsum_raised : (∑ i : κ, raised i) = L + C := by
    have hpoint :
        (fun i : κ => raised i) =
          fun i : κ => lower i + if i = high then C else 0 := by
      funext i
      by_cases hi : i = high
      · subst hi
        simp [raised]
      · simp [raised, hi]
    calc
      (∑ i : κ, raised i)
          = ∑ i : κ, (lower i + if i = high then C else 0) := by
              rw [hpoint]
      _ = (∑ i : κ, lower i) +
            ∑ i : κ, (if i = high then C else 0) := by
              rw [Finset.sum_add_distrib]
      _ = L + C := by
              rw [hlower]
              congr 1
              exact Fintype.sum_ite_eq' high (fun _i : κ => C)
  have hL_add_C_le_N : L + C ≤ N := by
    rw [← ha, ← hsum_raised]
    exact hsum_raised_le
  exact (not_lt_of_ge hL_add_C_le_N) hNlt

theorem exists_high_of_low
    {κ : Type*} [Fintype κ]
    (a lower upper : κ → ℕ) {N U C : ℕ} (low : κ)
    (ha : (∑ i : κ, a i) = N)
    (hupper : (∑ i : κ, upper i) = U)
    (hUlt : U < N + C)
    (horder : ∀ i, lower i ≤ upper i)
    (hlow : a low + C ≤ lower low) :
    ∃ high, upper high < a high := by
  classical
  by_contra hnone
  have hall : ∀ i, a i ≤ upper i := by
    intro i
    exact le_of_not_gt (by
      intro hlt
      exact hnone ⟨i, hlt⟩)
  let raised : κ → ℕ := fun i => if i = low then a low + C else a i
  have hraised_le : ∀ i, raised i ≤ upper i := by
    intro i
    by_cases hi : i = low
    · have hlow_i : a i + C ≤ lower i := by
        simpa [hi] using hlow
      simpa [raised, hi] using le_trans hlow_i (horder i)
    · simp [raised, hi, hall i]
  have hsum_raised_le : (∑ i : κ, raised i) ≤ ∑ i : κ, upper i :=
    Finset.sum_le_sum (by
      intro i _hi
      exact hraised_le i)
  have hsum_raised : (∑ i : κ, raised i) = N + C := by
    have hpoint :
        (fun i : κ => raised i) =
          fun i : κ => a i + if i = low then C else 0 := by
      funext i
      by_cases hi : i = low
      · subst hi
        simp [raised]
      · simp [raised, hi]
    calc
      (∑ i : κ, raised i)
          = ∑ i : κ, (a i + if i = low then C else 0) := by
              rw [hpoint]
      _ = (∑ i : κ, a i) +
            ∑ i : κ, (if i = low then C else 0) := by
              rw [Finset.sum_add_distrib]
      _ = N + C := by
              rw [ha]
              congr 1
              exact Fintype.sum_ite_eq' low (fun _i : κ => C)
  have hN_add_C_le_U : N + C ≤ U := by
    calc
      N + C = ∑ i : κ, raised i := hsum_raised.symm
      _ ≤ ∑ i : κ, upper i := hsum_raised_le
      _ = U := hupper
  exact (not_lt_of_ge hN_add_C_le_U) hUlt

/--
If there is no crossing between lower and upper anchors, no coordinate can be
above its upper anchor by as much as the number of coordinates.
-/
theorem count_lt_upper_add_card
    {κ : Type*} [Fintype κ]
    (a lower upper : κ → ℕ) {N L : ℕ} (t : κ)
    (ha : (∑ i : κ, a i) = N)
    (hlower : (∑ i : κ, lower i) = L)
    (hNlt : N < L + Fintype.card κ + 1)
    (horder : ∀ i, lower i ≤ upper i)
    (hno : NoRoundingCrossingBetween a lower upper) :
    a t < upper t + Fintype.card κ + 1 := by
  by_contra hnot
  have hhigh : upper t + Fintype.card κ + 1 ≤ a t := le_of_not_gt hnot
  have hNlt' : N < L + Fintype.card κ + 1 := hNlt
  obtain ⟨low, hlow_lt⟩ :=
    exists_low_of_high (C := Fintype.card κ + 1) a lower upper t ha hlower hNlt' horder hhigh
  have hcard_pos : 0 < Fintype.card κ + 1 := by omega
  have hhigh_one : upper t + 1 ≤ a t := by omega
  have hlow_one : a low + 1 ≤ lower low := Nat.succ_le_of_lt hlow_lt
  exact hno t low ⟨hhigh_one, hlow_one⟩

/--
If there is no crossing between lower and upper anchors, no coordinate can be
below its lower anchor by as much as the number of coordinates.
-/
theorem lower_lt_count_add_card
    {κ : Type*} [Fintype κ]
    (a lower upper : κ → ℕ) {N U : ℕ} (t : κ)
    (ha : (∑ i : κ, a i) = N)
    (hupper : (∑ i : κ, upper i) = U)
    (hUlt : U < N + Fintype.card κ + 1)
    (horder : ∀ i, lower i ≤ upper i)
    (hno : NoRoundingCrossingBetween a lower upper) :
    lower t < a t + Fintype.card κ + 1 := by
  by_contra hnot
  have hlow : a t + Fintype.card κ + 1 ≤ lower t := le_of_not_gt hnot
  obtain ⟨high, hhigh_lt⟩ :=
    exists_high_of_low (C := Fintype.card κ + 1) a lower upper t ha hupper hUlt horder hlow
  have hhigh_one : upper high + 1 ≤ a high :=
    Nat.succ_le_of_lt hhigh_lt
  have hlow_one : a t + 1 ≤ lower t := by omega
  exact hno high t ⟨hhigh_one, hlow_one⟩

/--
Two-sided coordinate closeness from a no-crossing certificate between lower
and upper integer anchors.
-/
theorem count_close
    {κ : Type*} [Fintype κ]
    (a lower upper : κ → ℕ) {N L U : ℕ}
    (ha : (∑ i : κ, a i) = N)
    (hlower : (∑ i : κ, lower i) = L)
    (hupper : (∑ i : κ, upper i) = U)
    (hNlt : N < L + Fintype.card κ + 1)
    (hUlt : U < N + Fintype.card κ + 1)
    (horder : ∀ i, lower i ≤ upper i)
    (hno : NoRoundingCrossingBetween a lower upper) :
    ∀ i : κ,
      lower i < a i + Fintype.card κ + 1 ∧
        a i < upper i + Fintype.card κ + 1 := by
  intro i
  exact
    ⟨lower_lt_count_add_card a lower upper i ha hupper hUlt horder hno,
      count_lt_upper_add_card a lower upper i ha hlower hNlt horder hno⟩

/--
Non-strict form of `count_close`.

This is often the more convenient finite-rounding estimate after turning a
strict natural inequality into an additive real error bound.
-/
theorem count_le_close
    {κ : Type*} [Fintype κ]
    (a lower upper : κ → ℕ) {N L U : ℕ}
    (ha : (∑ i : κ, a i) = N)
    (hlower : (∑ i : κ, lower i) = L)
    (hupper : (∑ i : κ, upper i) = U)
    (hNlt : N < L + Fintype.card κ + 1)
    (hUlt : U < N + Fintype.card κ + 1)
    (horder : ∀ i, lower i ≤ upper i)
    (hno : NoRoundingCrossingBetween a lower upper) :
    ∀ i : κ,
      lower i ≤ a i + Fintype.card κ ∧
        a i ≤ upper i + Fintype.card κ := by
  intro i
  have hi :=
    count_close a lower upper ha hlower hupper hNlt hUlt horder hno i
  omega

end NoRoundingCrossingBetween

/-! ### Real thresholds and integer majorants -/

/--
An integer majorant satisfying a nonnegative scaled budget exists exactly when
the ceiling majorant satisfies that budget.  This isolates the precise
rounding condition needed when a discrete tail proof is applied to a real
threshold.
-/
theorem exists_nat_majorant_mul_le_iff
    {alpha scale budget : ℝ} (hscale : 0 ≤ scale) :
    (∃ a : ℕ, alpha ≤ (a : ℝ) ∧ (a : ℝ) * scale ≤ budget) ↔
      (Nat.ceil alpha : ℝ) * scale ≤ budget := by
  constructor
  · rintro ⟨a, halpha, hbudget⟩
    have hceil_nat : Nat.ceil alpha ≤ a := (Nat.ceil_le).2 halpha
    have hceil_real : (Nat.ceil alpha : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hceil_nat
    exact (mul_le_mul_of_nonneg_right hceil_real hscale).trans hbudget
  · intro hbudget
    exact ⟨Nat.ceil alpha, Nat.le_ceil alpha, hbudget⟩

end FiniteRounding
end AppliedModelingLib
