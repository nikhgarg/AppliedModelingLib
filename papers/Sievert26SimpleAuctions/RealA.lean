import Sievert26SimpleAuctions.GroupAData

/-! Group `A` as genuine real-valued distributions. -/
set_option linter.deprecated false
open Finset

namespace Sievert26SimpleAuctions
namespace Data
variable (d : Data)

theorem W_posR : (0 : ℝ) < d.W := by exact_mod_cast d.W_pos
theorem Dn_posR : (0 : ℝ) < d.Dn := by exact_mod_cast d.Dn_pos

/-- item of type `i` -/
noncomputable def item (i : Fin 5) : FinDist where
  size := d.P i + d.e + 1
  val k := ((k : ℕ) : ℝ)
  prob k := (d.cf i k : ℝ) / d.W
  val_nonneg k := Nat.cast_nonneg _
  prob_nonneg k := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  prob_sum := by
    rw [← sum_div, div_eq_one_iff_eq d.W_posR.ne', ← Nat.cast_sum,
      Fin.sum_univ_eq_sum_range (fun k => d.cf i k), d.sum_cf]

/-- the whole group `A` : 5 types × 256 copies -/
noncomputable def DA (i : IA) : FinDist := d.item i.1

theorem prob_DA (ω : d.OA) : prob d.DA ω = (d.w ω : ℝ) / d.Dn := by
  change ∏ i : IA, ((d.cf i.1 (ω i) : ℝ) / d.W) = _
  rw [prod_div_distrib, prod_const, w, Nat.cast_prod, d.Dn_eq, Nat.cast_pow]
  simp

theorem value_DA (ω : d.OA) (i : IA) : value d.DA ω i = ((ω i : ℕ) : ℝ) := rfl

theorem tw_real (t : ℕ) :
    ((d.N : ℝ) + t) * ∑ ω : d.OA, (if t ≤ d.z ω then prob d.DA ω else 0) ≤ d.N := by
  have h : ∑ ω : d.OA, (if t ≤ d.z ω then prob d.DA ω else 0) = (d.tw t : ℝ) / d.Dn := by
    rw [tw, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun ω _ => ?_
    rw [prob_DA]
    split_ifs
    · rfl
    · rw [Nat.cast_zero, zero_div]
  rw [h, ← mul_div_assoc, div_le_iff₀ d.Dn_posR]
  exact_mod_cast d.tw_bound t

/-- Conditional on the other group having total value `y`. -/
theorem bundle_A (p y : ℝ) (hp : 0 ≤ p) :
    p * ∑ ω : Profile d.DA, (if p ≤ (∑ i, value d.DA ω i) + y then prob d.DA ω else 0)
      ≤ max (d.N : ℝ) y := by
  have hN : (0:ℝ) < d.N := by exact_mod_cast d.N_pos
  set q := ∑ ω : Profile d.DA, (if p ≤ (∑ i, value d.DA ω i) + y then prob d.DA ω else 0) with hq
  have hq0 : 0 ≤ q := sum_nonneg fun ω _ => by
    split_ifs
    · exact prob_nonneg _ _
    · exact le_rfl
  have hq1 : q ≤ 1 := by
    rw [← prob_sum d.DA]
    refine sum_le_sum fun ω _ => ?_
    split_ifs
    · exact le_rfl
    · exact prob_nonneg _ _
  by_cases hpy : p ≤ y
  · refine le_trans ?_ (le_max_right _ _)
    nlinarith
  · push Not at hpy
    set t := ⌈p - y⌉₊ with ht
    have hz : ∀ ω : d.OA, (∑ i, value d.DA ω i) = (d.z ω : ℝ) := by
      intro ω; rw [z, Nat.cast_sum]; rfl
    have hqt : q = ∑ ω : d.OA, (if t ≤ d.z ω then prob d.DA ω else 0) := by
      rw [hq]
      refine sum_congr rfl fun ω _ => ?_
      have : (p ≤ (∑ i, value d.DA ω i) + y) ↔ t ≤ d.z ω := by
        rw [hz ω, ht, Nat.ceil_le]
        constructor <;> intro h <;> linarith
      by_cases h : t ≤ d.z ω
      · rw [if_pos h, if_pos (this.mpr h)]
      · rw [if_neg h, if_neg (fun hh => h (this.mp hh))]
    have h1 := d.tw_real t
    rw [← hqt] at h1
    have h2 : p - y ≤ t := Nat.le_ceil _
    have h3 : p * q ≤ (y + t) * q := mul_le_mul_of_nonneg_right (by linarith) hq0
    rcases le_total y d.N with h | h
    · refine le_trans ?_ (le_max_left _ _)
      nlinarith
    · refine le_trans ?_ (le_max_right _ _)
      nlinarith [mul_le_mul_of_nonneg_left hq1 (sub_nonneg.mpr h)]

theorem item_rev_le (i : Fin 5) : (d.item i).rev ≤ (d.R i : ℝ) / d.W := by
  refine FinDist.rev_le _ _ fun p hp => ?_
  have h : (d.item i).tail p =
      ((∑ k ∈ range (d.P i + d.e + 1), if ⌈p⌉₊ ≤ k then d.cf i k else 0 : ℕ) : ℝ) / d.W := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => if ⌈p⌉₊ ≤ k then d.cf i k else 0),
      Nat.cast_sum, sum_div]
    change ∑ k : Fin (d.P i + d.e + 1),
      (if p ≤ ((k : ℕ) : ℝ) then (d.cf i k : ℝ) / d.W else 0) = _
    refine sum_congr rfl fun k _ => ?_
    by_cases h : p ≤ ((k : ℕ) : ℝ)
    · rw [if_pos h, if_pos (Nat.ceil_le.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (Nat.ceil_le.mp hh))]; simp
  rw [h, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ d.W_posR.le
  have h2 := d.tail_le i ⌈p⌉₊ (d.P i + d.e + 1)
  calc p * _ ≤ (⌈p⌉₊ : ℝ) * _ := mul_le_mul_of_nonneg_right (Nat.le_ceil p) (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast h2

theorem SREV_A : SREV d.DA ≤ d.N := by
  have h1 : SREV d.DA ≤ ∑ i : IA, (d.R i.1 : ℝ) / d.W :=
    sum_le_sum fun i _ => d.item_rev_le i.1
  refine h1.trans ?_
  rw [← sum_div, div_le_iff₀ d.W_posR, Fintype.sum_prod_type, Fin.sum_univ_five]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := d.R_sum
  have h2 : (256 * (d.R 0 + d.R 1 + d.R 2 + d.R 3 + d.R 4) : ℝ) ≤ d.N * d.W := by
    exact_mod_cast this
  push_cast
  linarith

/-- payment to the entry-fee mechanism with item prices -/
noncomputable def payFun (v : IA → ℝ) : ℝ :=
  if (d.e : ℝ) ≤ ∑ i : IA, max (v i - d.P i.1) 0 then
    d.e + ∑ i : IA, (if (d.P i.1 : ℝ) ≤ v i then (d.P i.1 : ℝ) else 0) else 0

theorem rev_A : (119464 / 100000 : ℝ) * d.N ≤
    ∑ ω : Profile d.DA, prob d.DA ω * d.payFun (value d.DA ω) := by
  have h : ∀ ω : d.OA, prob d.DA ω * d.payFun (value d.DA ω) =
      ((if d.e ≤ d.sp ω then d.w2 ω else 0 : ℕ) : ℝ) / d.Dn := by
    intro ω
    have hs : ∑ i : IA, max (value d.DA ω i - d.P i.1) 0 = (d.sp ω : ℝ) := by
      rw [sp, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [value_DA]
      rcases le_total (d.P i.1) (ω i : ℕ) with h | h
      · rw [Nat.cast_sub h, max_eq_left]
        have : (d.P i.1 : ℝ) ≤ ((ω i : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, max_eq_right]
        have : ((ω i : ℕ) : ℝ) ≤ (d.P i.1 : ℝ) := by exact_mod_cast h
        linarith
    have hpy : ∑ i : IA, (if (d.P i.1 : ℝ) ≤ value d.DA ω i then (d.P i.1 : ℝ) else 0)
        = (d.py ω : ℝ) := by
      rw [py, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [value_DA]
      by_cases h : d.P i.1 ≤ (ω i : ℕ)
      · rw [if_pos h, if_pos (by exact_mod_cast h)]
      · rw [if_neg h, if_neg (by exact_mod_cast h)]; simp
    rw [payFun, hs, hpy, prob_DA]
    by_cases he : d.e ≤ d.sp ω
    · rw [if_pos he, if_pos (by exact_mod_cast he), w2]
      push_cast; ring
    · rw [if_neg he, if_neg (by exact_mod_cast he), mul_zero, Nat.cast_zero, zero_div]
  have h2 : ∑ ω : Profile d.DA, prob d.DA ω * d.payFun (value d.DA ω) =
      ((∑ ω : d.OA, if d.e ≤ d.sp ω then d.w2 ω else 0 : ℕ) : ℝ) / d.Dn := by
    rw [Nat.cast_sum, sum_div]
    exact sum_congr rfl fun ω _ => h ω
  rw [h2, le_div_iff₀ d.Dn_posR]
  have h3 : (119464 * (d.N * d.Dn) : ℝ) ≤
      100000 * ((∑ ω : d.OA, if d.e ≤ d.sp ω then d.w2 ω else 0 : ℕ) : ℝ) := by
    exact_mod_cast d.rev_nat
  linarith

end Data
end Sievert26SimpleAuctions
