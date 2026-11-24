import Sievert26SimpleAuctions.GroupAData

/-!
Group `B`: `L^2` iid equal-revenue items whose sum concentrates around `c` while the separate
revenue `c / H_L` vanishes (`H_L` harmonic number).
-/
set_option linter.deprecated false
open Finset

namespace Sievert26SimpleAuctions
namespace GroupB

/-- harmonic number -/
noncomputable def H (L : ℕ) : ℝ := ∑ j ∈ range L, 1 / ((j : ℝ) + 1)

noncomputable def tau (L j : ℕ) : ℝ := if j < L then 1 / ((j : ℝ) + 1) else 0

theorem tau_anti (L j : ℕ) : tau L (j+1) ≤ tau L j := by
  unfold tau
  have h1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
  split_ifs with h2 h3
  · apply one_div_le_one_div_of_le h1; push_cast; linarith
  · omega
  · positivity
  · exact le_rfl

theorem tau_le (L j : ℕ) : tau L j ≤ 1 / ((j : ℝ) + 1) := by
  unfold tau; split_ifs
  · exact le_rfl
  · positivity

theorem tau_nonneg (L j : ℕ) : 0 ≤ tau L j := by
  unfold tau; split_ifs
  · positivity
  · exact le_rfl

theorem tau_L (L : ℕ) : tau L L = 0 := by unfold tau; rw [if_neg (by omega)]

noncomputable def pr (L j : ℕ) : ℝ := tau L j - tau L (j+1)

theorem pr_nonneg (L j : ℕ) : 0 ≤ pr L j := sub_nonneg.mpr (tau_anti L j)

theorem sum_pr_aux (L n : ℕ) : ∑ j ∈ range n, pr L j = tau L 0 - tau L n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pr]; ring

theorem sum_pr (L : ℕ) (hL : 0 < L) : ∑ j ∈ range L, pr L j = 1 := by
  rw [sum_pr_aux, tau_L, tau, if_pos hL]; simp

theorem sum_tau (L : ℕ) : ∑ j ∈ range L, tau L j = H L :=
  sum_congr rfl fun j hj => by rw [tau, if_pos (mem_range.mp hj)]

theorem mean_aux (L n : ℕ) :
    ∑ j ∈ range n, pr L j * ((j:ℝ) + 1) = ∑ j ∈ range n, tau L j - n * tau L n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ, pr]; push_cast; ring

theorem mean_pr (L : ℕ) : ∑ j ∈ range L, pr L j * ((j:ℝ) + 1) = H L := by
  rw [mean_aux, tau_L, sum_tau]; ring

theorem second_aux (L n : ℕ) : ∑ j ∈ range n, pr L j * ((j:ℝ) + 1) ^ 2 =
    ∑ j ∈ range n, (2 * (j:ℝ) + 1) * tau L j - (n:ℝ) ^ 2 * tau L n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ, pr]; push_cast; ring

theorem second_pr (L : ℕ) : ∑ j ∈ range L, pr L j * ((j:ℝ) + 1) ^ 2 ≤ 2 * (L : ℝ) := by
  rw [second_aux, tau_L, mul_zero, sub_zero]
  have : ∀ j ∈ range L, (2 * (j:ℝ) + 1) * tau L j ≤ 2 := by
    intro j _
    have h1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
    calc (2 * (j:ℝ) + 1) * tau L j ≤ (2 * (j:ℝ) + 1) * (1 / ((j:ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (tau_le L j) (by positivity)
      _ ≤ 2 := by rw [mul_one_div, div_le_iff₀ h1]; linarith
  calc _ ≤ ∑ j ∈ range L, (2:ℝ) := sum_le_sum this
    _ = 2 * (L : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem tail_pr (L m n : ℕ) : ∑ j ∈ range n, (if m ≤ j then pr L j else 0) ≤ tau L m := by
  suffices h : ∑ j ∈ range n, (if m ≤ j then pr L j else 0) +
      (if m ≤ n then tau L n else tau L m) = tau L m by
    have : 0 ≤ (if m ≤ n then tau L n else tau L m) := by split_ifs <;> exact tau_nonneg _ _
    linarith
  induction n with
  | zero =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · rw [if_neg (by omega)]; simp
  | succ n ih =>
    rw [sum_range_succ]
    rcases lt_trichotomy m (n+1) with h | h | h
    · rw [if_pos (show m ≤ n by omega)] at ih ⊢
      rw [if_pos (show m ≤ n + 1 by omega), ← ih, pr]; ring
    · rw [if_neg (show ¬ m ≤ n by omega)] at ih ⊢
      rw [if_pos (show m ≤ n + 1 by omega), ← h]; linarith
    · rw [if_neg (show ¬ m ≤ n by omega)] at ih ⊢
      rw [if_neg (show ¬ m ≤ n + 1 by omega)]; linarith

section
variable (L : ℕ) (hL : 0 < L) (δ : ℝ) (hδ : 0 < δ)

/-- one item of group `B` -/
noncomputable def item : FinDist where
  size := L
  val k := (((k : ℕ) : ℝ) + 1) * δ
  prob k := pr L k
  val_nonneg k := by positivity
  prob_nonneg k := pr_nonneg _ _
  prob_sum := by rw [Fin.sum_univ_eq_sum_range (fun k => pr L k), sum_pr L hL]

theorem item_rev_le : (item L hL δ hδ).rev ≤ δ := by
  refine FinDist.rev_le _ _ fun p hp => ?_
  set m := ⌈p / δ⌉₊ - 1 with hm
  have h : (item L hL δ hδ).tail p = ∑ j ∈ range L, (if m ≤ j then pr L j else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if m ≤ j then pr L j else 0)]
    change ∑ k : Fin L, (if p ≤ (((k : ℕ) : ℝ) + 1) * δ then pr L k else 0) = _
    refine sum_congr rfl fun k _ => ?_
    have : p ≤ (((k : ℕ) : ℝ) + 1) * δ ↔ m ≤ (k : ℕ) := by
      rw [← div_le_iff₀ hδ]
      have h1 : p / δ ≤ ((k : ℕ) : ℝ) + 1 ↔ ⌈p / δ⌉₊ ≤ (k : ℕ) + 1 := by
        rw [Nat.ceil_le]; push_cast; exact Iff.rfl
      rw [h1]; omega
    by_cases hh : m ≤ (k : ℕ)
    · rw [if_pos hh, if_pos (this.mpr hh)]
    · rw [if_neg hh, if_neg (fun h' => hh (this.mp h'))]
  rw [h]
  have h2 : p ≤ ((m : ℝ) + 1) * δ := by
    rw [← div_le_iff₀ hδ]
    have : ⌈p / δ⌉₊ ≤ m + 1 := by omega
    calc p / δ ≤ (⌈p / δ⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = _ := by push_cast; ring
  have h3 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  calc p * _ ≤ p * (1 / ((m:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left ((tail_pr L m L).trans (tau_le L m)) hp
    _ ≤ (((m:ℝ) + 1) * δ) * (1 / ((m:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = δ := by field_simp

variable (M : ℕ)

/-- group `B` with `M` iid items -/
noncomputable def DB (_ : Fin M) : FinDist := item L hL δ hδ

theorem SREV_B : SREV (DB L hL δ hδ M) ≤ M * δ := by
  calc SREV (DB L hL δ hδ M) ≤ ∑ _i : Fin M, δ := sum_le_sum fun i _ => item_rev_le L hL δ hδ
    _ = M * δ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

abbrev OB : Type := (i : Fin M) → Fin L

theorem prob_DB (ω : OB L M) : prob (DB L hL δ hδ M) ω = ∏ i, pr L (ω i) := rfl
theorem value_DB (ω : OB L M) (i : Fin M) :
    value (DB L hL δ hδ M) ω i = (((ω i : ℕ) : ℝ) + 1) * δ := rfl

include hL in
theorem sum_pr_fin : ∑ k : Fin L, pr L k = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => pr L k), sum_pr L hL]

include hL in
theorem marg1 (f : ℕ → ℝ) (i : Fin M) :
    ∑ ω : OB L M, (∏ j, pr L (ω j)) * f (ω i) = ∑ k ∈ range L, pr L k * f k := by
  have h := sum_prod_marg (fun _ : Fin M => L) (fun _ k => pr L k) f i
  rw [h]
  simp only [sum_pr_fin L hL, prod_const_one, mul_one]
  exact Fin.sum_univ_eq_sum_range (fun k => pr L k * f k) L

include hL in
theorem marg2 (f : ℕ → ℝ) (hf : ∑ k ∈ range L, pr L k * f k = 0) (i j : Fin M) (hij : i ≠ j) :
    ∑ ω : OB L M, (∏ l, pr L (ω l)) * (f (ω i) * f (ω j)) = 0 := by
  have h := sum_prod_marg (fun _ : Fin M => L)
    (fun l k => pr L k * if l = i then f k else 1) f j
  have h1 : ∀ ω : OB L M, (∏ l, pr L (ω l)) * (f (ω i) * f (ω j)) =
      (∏ l, (pr L (ω l) * if l = i then f (ω l) else 1)) * f (ω j) := by
    intro ω
    rw [prod_mul_distrib, prod_ite_eq' univ i]
    simp; ring
  simp_rw [h1]
  rw [h, prod_eq_zero (mem_erase.mpr ⟨hij, mem_univ i⟩), mul_zero]
  simp only [if_true]
  rw [Fin.sum_univ_eq_sum_range (fun k => pr L k * f k) L, hf]

/-- total value of group `B` -/
noncomputable def ZB (ω : OB L M) : ℝ := ∑ i, value (DB L hL δ hδ M) ω i

/-- Second central moment of the total value. -/
theorem variance_B : ∑ ω : OB L M, prob (DB L hL δ hδ M) ω *
    (ZB L hL δ hδ M ω - M * (H L * δ)) ^ 2 ≤ M * (2 * L * δ ^ 2) := by
  set f : ℕ → ℝ := fun k => ((k:ℝ) + 1) * δ - H L * δ with hf
  have hf0 : ∑ k ∈ range L, pr L k * f k = 0 := by
    have : ∀ k ∈ range L, pr L k * f k = (pr L k * ((k:ℝ)+1)) * δ - pr L k * (H L * δ) := by
      intro k _; rw [hf]; ring
    rw [sum_congr rfl this, sum_sub_distrib, ← sum_mul, ← sum_mul, mean_pr, sum_pr L hL]; ring
  have hf2 : ∑ k ∈ range L, pr L k * (f k * f k) ≤ 2 * L * δ ^ 2 := by
    have h1 : ∑ k ∈ range L, pr L k * (f k * f k) =
        (∑ k ∈ range L, pr L k * ((k:ℝ)+1)^2) * δ^2 - (H L * δ) ^ 2 := by
      have : ∀ k ∈ range L, pr L k * (f k * f k) = (pr L k * ((k:ℝ)+1)^2) * δ^2
          - (pr L k * ((k:ℝ)+1)) * (2 * H L * δ^2) + pr L k * (H L * δ)^2 := by
        intro k _; rw [hf]; ring
      rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul, ← sum_mul,
        mean_pr, sum_pr L hL]; ring
    rw [h1]
    have := mul_le_mul_of_nonneg_right (second_pr L) (sq_nonneg δ)
    nlinarith [sq_nonneg (H L * δ)]
  have hZ : ∀ ω : OB L M, ZB L hL δ hδ M ω - M * (H L * δ) = ∑ i, f (ω i) := by
    intro ω
    rw [ZB, hf, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  have h1 : ∀ ω : OB L M, prob (DB L hL δ hδ M) ω * (ZB L hL δ hδ M ω - M * (H L * δ)) ^ 2 =
      ∑ i, ∑ j, (∏ l, pr L (ω l)) * (f (ω i) * f (ω j)) := by
    intro ω
    rw [hZ, prob_DB, sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun i _ => by rw [mul_sum]
  simp_rw [h1]
  rw [sum_comm]
  have h2 : ∀ i : Fin M, ∑ ω : OB L M, ∑ j, (∏ l, pr L (ω l)) * (f (ω i) * f (ω j))
      ≤ 2 * L * δ ^ 2 := by
    intro i
    rw [sum_comm, sum_eq_single i]
    · rw [marg1 L hL M (fun k => f k * f k) i]; exact hf2
    · intro j _ hj; exact marg2 L hL M f hf0 i j (Ne.symm hj)
    · intro h; exact absurd (mem_univ i) h
  calc _ ≤ ∑ _i : Fin M, 2 * L * δ ^ 2 := sum_le_sum fun i _ => h2 i
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end

theorem H_pos (L : ℕ) (hL : 0 < L) : 1 ≤ H L := by
  have h : ∑ j ∈ range 1, 1 / ((j:ℝ)+1) ≤ H L :=
    sum_le_sum_of_subset_of_nonneg (range_mono hL) fun j _ _ => by positivity
  simpa using h

theorem H_tendsto : Filter.Tendsto H Filter.atTop Filter.atTop := by
  have h : H = fun n => ∑ i ∈ range n, 1 / ((i:ℝ) + 1) := rfl
  rw [h]
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

end GroupB
end Sievert26SimpleAuctions
