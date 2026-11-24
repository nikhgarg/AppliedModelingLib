import Sievert26SimpleAuctions.Main
import Sievert26SimpleAuctions.Expect
import Sievert26SimpleAuctions.IID100Kernel

/-!
# 100-item i.i.d. lower bound (Proposition 5)

100 i.i.d. items with `Pr[X >= k] = 3 / (25 * max(k, 4))` for `1 <= k <= 13` and `0` for `k > 13`.
Entry fee `9` and item price `4` achieve `REV / max(SREV, BREV) >= 1.324907`.
-/
set_option linter.deprecated false
open Finset

namespace Sievert26SimpleAuctions

/-- Abstract record of all numerical facts for the 100-item i.i.d. instance. -/
structure IID100Data where
  (W X Dn gz gw hw Fz YwM qloss : ℕ)
  (cN : ℕ → ℕ)
  W_pos : 0 < W
  W_val : 25 * 360360 = 3 * W
  Dn_eq : Dn = W ^ 100
  Fz_eq : Fz = gz ^ 100
  YwM_eq : YwM = (9 * gw ^ 100 + 100 * (hw * gw ^ 99)) % X ^ 9
  qloss_eq : qloss = ∑ j ∈ range 9, YwM / X ^ j % X
  sum_c : ∑ k : Fin 14, cN k = W
  sum_cz : ∑ k : Fin 14, cN k * X ^ (k : ℕ) = gz
  sum_cw : ∑ k : Fin 14, cN k * X ^ ((k : ℕ) - 4) = gw
  sum_ch : ∑ k : Fin 14, cN k * X ^ ((k : ℕ) - 4) * (if 4 ≤ (k : ℕ) then 4 else 0) = hw
  sum_cp : ∑ k : Fin 14, cN k * (if 4 ≤ (k : ℕ) then 4 else 0) = 4 * 90090
  tail_check : ∀ m : Fin 15, (m : ℕ) * (∑ k : Fin 14, if (m : ℕ) ≤ (k : ℕ) then cN k else 0) ≤ 360360
  tail_exact : ∀ m : Fin 14, 1 ≤ (m : ℕ) →
    (∑ k : Fin 14, if (m : ℕ) ≤ (k : ℕ) then cN k else 0) * (25 * max (m : ℕ) 4) = 3 * W
  Dn_lt_X : Dn < X
  bound_X : (9 * W + 400 * 90090) * W ^ 99 < X
  brev_ok : IID100Cert.loop X Dn 1301 0 0 Fz = true
  rev_ok : 15985442 * Dn + 1000000 * qloss ≤ 1000000 * ((9 * W + 400 * 90090) * W ^ 99)

namespace IID100Data
variable (d : IID100Data)

abbrev O : Type := Fin 100 → Fin 14

def wt (ω : O) : ℕ := ∏ i, d.cN (ω i)
def zz (ω : O) : ℕ := ∑ i, (ω i : ℕ)
def spl (ω : O) : ℕ := ∑ i, ((ω i : ℕ) - 4)
def py (ω : O) : ℕ := ∑ i, if 4 ≤ (ω i : ℕ) then 4 else 0

theorem sum_wt : ∑ ω, d.wt ω = d.Dn := by
  unfold wt
  rw [sum_prod_pi (fun (_ : Fin 100) (k : Fin 14) => d.cN k)]
  simp only [d.sum_c, prod_const, card_univ, Fintype.card_fin, d.Dn_eq]

theorem gen_z : ∑ ω, d.wt ω * d.X ^ zz ω = d.Fz := by
  have h1 : ∀ ω : O, d.wt ω * d.X ^ zz ω = ∏ i, (d.cN (ω i) * d.X ^ (ω i : ℕ)) := by
    intro ω; rw [wt, zz, prod_mul_distrib, prod_pow_eq_pow_sum]
  simp_rw [h1]
  rw [sum_prod_pi (fun (_ : Fin 100) (k : Fin 14) => d.cN k * d.X ^ (k : ℕ))]
  simp only [d.sum_cz, prod_const, card_univ, Fintype.card_fin, d.Fz_eq]

def a (t : ℕ) : ℕ := ∑ ω, if zz ω = t then d.wt ω else 0

theorem digit_a (t : ℕ) : d.Fz / d.X ^ t % d.X = d.a t := by
  rw [← d.gen_z]
  exact Cert.digit_sum d.wt zz d.X (by rw [d.sum_wt]; exact d.Dn_lt_X) t

theorem loop_sound (F : ℕ) (b : ℕ → ℕ) (hF : ∀ t, F / d.X ^ t % d.X = b t) (f : ℕ) : ∀ t,
    IID100Cert.loop d.X d.Dn f t (∑ i ∈ range t, b i) (F / d.X ^ t) = true →
    ∀ j < f, (t + j) * (d.Dn - ∑ i ∈ range (t + j), b i) * 1000000 ≤ 12065329 * d.Dn := by
  induction f with
  | zero => intro t _ j hj; omega
  | succ f ih =>
    intro t h j hj
    rw [IID100Cert.loop, Bool.and_eq_true] at h
    rcases j with _ | j
    · exact Nat.le_of_ble_eq_true h.1
    · have h2 := h.2
      rw [hF, ← sum_range_succ, Nat.div_div_eq_div_mul, ← pow_succ] at h2
      have := ih (t+1) h2 j (by omega)
      rwa [show t + 1 + j = t + (j + 1) by ring] at this

def tw (t : ℕ) : ℕ := ∑ ω, if t ≤ zz ω then d.wt ω else 0

theorem tw_add (t : ℕ) : d.tw t + ∑ i ∈ range t, d.a i = d.Dn := by
  unfold tw a
  rw [sum_comm, ← sum_add_distrib, ← d.sum_wt]
  refine sum_congr rfl fun ω _ => ?_
  rw [sum_ite_eq (range t) (zz ω) (fun _ => d.wt ω)]
  by_cases h : t ≤ zz ω
  · rw [if_pos h, if_neg (by rw [mem_range]; omega), add_zero]
  · rw [if_neg h, if_pos (by rw [mem_range]; omega), zero_add]

theorem zz_le (ω : O) : zz ω ≤ 1300 := by
  unfold zz
  calc ∑ i, (ω i : ℕ) ≤ ∑ _i : Fin 100, 13 := sum_le_sum fun i _ => by have := (ω i).isLt; omega
    _ = 1300 := by simp

theorem tw_bound (t : ℕ) : t * d.tw t * 1000000 ≤ 12065329 * d.Dn := by
  by_cases ht : t ≤ 1300
  · have h := d.loop_sound d.Fz d.a d.digit_a 1301 0
      (by rw [sum_range_zero, pow_zero, Nat.div_one]; exact d.brev_ok) t (by omega)
    rw [zero_add] at h
    have h2 := d.tw_add t
    rwa [show d.Dn - ∑ i ∈ range t, d.a i = d.tw t by omega] at h
  · have : d.tw t = 0 := by
      unfold tw
      refine sum_eq_zero fun ω _ => ?_
      rw [if_neg (by have := zz_le ω; omega)]
    rw [this]; simp

/-! ### Revenue -/
def w2 (ω : O) : ℕ := d.wt ω * (9 + py ω)

theorem wt_spl (ω : O) : d.wt ω * d.X ^ spl ω = ∏ i, (d.cN (ω i) * d.X ^ ((ω i : ℕ) - 4)) := by
  rw [wt, spl, prod_mul_distrib, prod_pow_eq_pow_sum]

theorem gen_w : ∑ ω, d.wt ω * d.X ^ spl ω = d.gw ^ 100 := by
  simp_rw [d.wt_spl]
  rw [sum_prod_pi (fun (_ : Fin 100) (k : Fin 14) => d.cN k * d.X ^ ((k : ℕ) - 4))]
  simp only [d.sum_cw, prod_const, card_univ, Fintype.card_fin]

theorem gen_p (i : Fin 100) : ∑ ω, (d.wt ω * d.X ^ spl ω) * (if 4 ≤ (ω i : ℕ) then 4 else 0) =
    d.hw * d.gw ^ 99 := by
  simp_rw [d.wt_spl]
  have h := sum_prod_marg (fun _ : Fin 100 => 14) (fun _ k => d.cN k * d.X ^ (k - 4))
    (fun k => if 4 ≤ k then 4 else 0) i
  rw [h]
  simp only [d.sum_cw, d.sum_ch, prod_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]

theorem gen_y : ∑ ω, d.w2 ω * d.X ^ spl ω = 9 * d.gw ^ 100 + 100 * (d.hw * d.gw ^ 99) := by
  have h1 : ∀ ω : O, d.w2 ω * d.X ^ spl ω = 9 * (d.wt ω * d.X ^ spl ω) +
      ∑ i, (d.wt ω * d.X ^ spl ω) * (if 4 ≤ (ω i : ℕ) then 4 else 0) := by
    intro ω; rw [w2, py, ← mul_sum]; ring
  simp_rw [h1]
  rw [sum_add_distrib, ← mul_sum, d.gen_w, sum_comm]
  simp_rw [d.gen_p]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem sum_w2 : ∑ ω, d.w2 ω = (9 * d.W + 400 * 90090) * d.W ^ 99 := by
  have h1 : ∀ ω : O, d.w2 ω = 9 * d.wt ω + ∑ i, d.wt ω * (if 4 ≤ (ω i : ℕ) then 4 else 0) := by
    intro ω; rw [w2, py, ← mul_sum]; ring
  have h2 : ∀ i : Fin 100, ∑ ω, d.wt ω * (if 4 ≤ (ω i : ℕ) then 4 else 0) =
      4 * 90090 * d.W ^ 99 := by
    intro i
    unfold wt
    have h := sum_prod_marg (fun _ : Fin 100 => 14) (fun _ k => d.cN k)
      (fun k => if 4 ≤ k then 4 else 0) i
    rw [h]
    simp only [d.sum_c, d.sum_cp, prod_const, card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin]
  simp_rw [h1]
  rw [sum_add_distrib, ← mul_sum, d.sum_wt, sum_comm]
  simp_rw [h2]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, d.Dn_eq,
    show (100 : ℕ) = 99 + 1 from rfl, pow_succ]
  ring

theorem digit_y (j : ℕ) (hj : j < 9) : d.YwM / d.X ^ j % d.X = ∑ ω, if spl ω = j then d.w2 ω else 0 := by
  rw [d.YwM_eq, Cert.mod_digit _ _ _ _ hj, ← d.gen_y]
  exact Cert.digit_sum d.w2 spl d.X (by rw [d.sum_w2]; exact d.bound_X) j

theorem rev_nat : 15985442 * d.Dn ≤ 1000000 * ∑ ω, if 9 ≤ spl ω then d.w2 ω else 0 := by
  have h := d.rev_ok
  rw [← d.sum_w2] at h
  have hq : d.qloss = ∑ ω, if spl ω < 9 then d.w2 ω else 0 := by
    rw [d.qloss_eq]
    rw [sum_congr rfl (fun j hj => d.digit_y j (mem_range.mp hj)), sum_comm]
    refine sum_congr rfl fun ω _ => ?_
    rw [sum_ite_eq (range 9) (spl ω) (fun _ => d.w2 ω)]
    simp only [mem_range]
  have h2 : (∑ ω, if 9 ≤ spl ω then d.w2 ω else 0) + d.qloss = ∑ ω, d.w2 ω := by
    rw [hq, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ => ?_
    by_cases hh : 9 ≤ spl ω
    · rw [if_pos hh, if_neg (by omega), add_zero]
    · rw [if_neg hh, if_pos (by omega), zero_add]
  omega

/-! ### Real-valued statements -/
theorem W_posR : (0:ℝ) < (d.W : ℕ) := by exact_mod_cast d.W_pos
theorem Dn_posR : (0:ℝ) < (d.Dn : ℕ) := by
  rw [d.Dn_eq, Nat.cast_pow]; exact pow_pos d.W_posR _

/-- The common item distribution for Proposition 5 (`n = 100`). -/
noncomputable def F : FinDist where
  size := 14
  val k := ((k : ℕ) : ℝ)
  prob k := (d.cN k : ℝ) / d.W
  val_nonneg k := Nat.cast_nonneg _
  prob_nonneg k := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  prob_sum := by
    rw [← sum_div, div_eq_one_iff_eq d.W_posR.ne', ← Nat.cast_sum, d.sum_c]

noncomputable def DF (_ : Fin 100) : FinDist := d.F

theorem F_tail_nat (m : ℕ) :
    d.F.tail (m : ℝ) = ((∑ k : Fin 14, if m ≤ (k : ℕ) then d.cN k else 0 : ℕ) : ℝ) / d.W := by
  rw [Nat.cast_sum, sum_div]
  change ∑ k : Fin 14, (if (m : ℝ) ≤ ((k : ℕ) : ℝ) then (d.cN k : ℝ) / d.W else 0) = _
  refine sum_congr rfl fun k _ => ?_
  by_cases h : m ≤ (k : ℕ)
  · rw [if_pos h, if_pos (by exact_mod_cast h)]
  · rw [if_neg h, if_neg (by exact_mod_cast h)]; simp

theorem F_tail_eq (m : ℕ) (h1 : 1 ≤ m) (h13 : m ≤ 13) :
    d.F.tail (m : ℝ) = (3 : ℝ) / (25 * max (m : ℝ) 4) := by
  rw [d.F_tail_nat]
  have hm : m < 14 := by omega
  have heq : ((∑ k : Fin 14, if m ≤ (k : ℕ) then d.cN k else 0 : ℕ) : ℝ) *
      (25 * max (m : ℝ) 4) = 3 * (d.W : ℝ) := by
    have hnat := d.tail_exact ⟨m, hm⟩ h1
    have hcast : ((∑ k : Fin 14, if m ≤ (k : ℕ) then d.cN k else 0 : ℕ) : ℝ) *
        ((25 * max m 4 : ℕ) : ℝ) = 3 * (d.W : ℝ) := by exact_mod_cast hnat
    simpa [Nat.cast_max] using hcast
  have hden : (0 : ℝ) < 25 * max (m : ℝ) 4 := by
    have : (4 : ℝ) ≤ max (m : ℝ) 4 := le_max_right _ _
    linarith
  rw [div_eq_div_iff d.W_posR.ne' hden.ne']
  linarith

theorem F_tail_gt13 (m : ℕ) (h13 : 13 < m) : d.F.tail (m : ℝ) = 0 := by
  rw [d.F_tail_nat]
  have : (∑ k : Fin 14, if m ≤ (k : ℕ) then d.cN k else 0) = 0 :=
    sum_eq_zero fun k _ => by rw [if_neg (by have := k.isLt; omega)]
  rw [this]; simp

theorem prob_DF (ω : O) : prob d.DF ω = (d.wt ω : ℝ) / d.Dn := by
  change ∏ i : Fin 100, ((d.cN (ω i) : ℝ) / d.W) = _
  rw [prod_div_distrib, prod_const, wt, Nat.cast_prod, d.Dn_eq, Nat.cast_pow]
  simp

theorem F_rev_le : d.F.rev ≤ 3 / 25 := by
  refine FinDist.rev_le _ _ fun p hp => ?_
  have h : d.F.tail p = ((∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0 : ℕ) : ℝ) / d.W := by
    rw [Nat.cast_sum, sum_div]
    change ∑ k : Fin 14, (if p ≤ ((k : ℕ) : ℝ) then (d.cN k : ℝ) / d.W else 0) = _
    refine sum_congr rfl fun k _ => ?_
    by_cases h : p ≤ ((k : ℕ) : ℝ)
    · rw [if_pos h, if_pos (Nat.ceil_le.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (Nat.ceil_le.mp hh))]; simp
  have hm : ⌈p⌉₊ * (∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0) ≤ 360360 := by
    by_cases hlt : ⌈p⌉₊ < 15
    · exact d.tail_check ⟨⌈p⌉₊, hlt⟩
    · have : (∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0) = 0 :=
        sum_eq_zero fun k _ => by rw [if_neg (by have := k.isLt; omega)]
      rw [this]; simp
  rw [h, ← mul_div_assoc, div_le_iff₀ d.W_posR]
  have h3 : (⌈p⌉₊ : ℝ) * ((∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0 : ℕ) : ℝ) ≤ 360360 := by
    exact_mod_cast hm
  have h4 := mul_le_mul_of_nonneg_right (Nat.le_ceil p)
    (Nat.cast_nonneg (α := ℝ) (∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0))
  have h5 : (25 * 360360 : ℝ) = 3 * (d.W : ℝ) := by exact_mod_cast d.W_val
  linarith

theorem F_rev_ge : (3 / 25 : ℝ) ≤ d.F.rev := by
  have h4 : (4 : ℝ) * d.F.tail (4 : ℝ) ≤ d.F.rev :=
    le_ciSup (f := fun p : {p : ℝ // 0 ≤ p} => (p : ℝ) * d.F.tail p) (FinDist.rev_bdd d.F)
      ⟨4, by norm_num⟩
  have ht := d.F_tail_eq 4 (by omega) (by omega)
  norm_num at ht
  linarith

theorem SREV_le : SREV d.DF ≤ 12 := by
  calc SREV d.DF ≤ ∑ _i : Fin 100, (3 / 25 : ℝ) := sum_le_sum fun _ _ => d.F_rev_le
    _ = 12 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num

theorem SREV_pos : (0 : ℝ) < SREV d.DF := by
  have h : (12 : ℝ) ≤ SREV d.DF := by
    calc (12 : ℝ) = ∑ _i : Fin 100, (3 / 25 : ℝ) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
      _ ≤ SREV d.DF := sum_le_sum fun _ _ => d.F_rev_ge
  linarith

theorem BREV_le' : BREV d.DF ≤ 12065329 / 1000000 := by
  refine BREV_le _ _ fun p hp => ?_
  have hz : ∀ ω : O, (∑ i, value d.DF ω i) = (zz ω : ℝ) := by
    intro ω; rw [zz, Nat.cast_sum]; rfl
  have h : bundleTail d.DF p = (d.tw ⌈p⌉₊ : ℝ) / d.Dn := by
    unfold bundleTail
    rw [tw, Nat.cast_sum, sum_div]
    change ∑ ω : O, (if p ≤ ∑ i, value d.DF ω i then prob d.DF ω else 0) = _
    refine sum_congr rfl fun ω _ => ?_
    rw [hz ω, d.prob_DF]
    by_cases h : p ≤ (zz ω : ℝ)
    · rw [if_pos h, if_pos (Nat.ceil_le.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (Nat.ceil_le.mp hh))]; simp
  rw [h, ← mul_div_assoc, div_le_iff₀ d.Dn_posR]
  have h1 : (⌈p⌉₊ : ℝ) * (d.tw ⌈p⌉₊ : ℝ) * 1000000 ≤ 12065329 * d.Dn := by
    exact_mod_cast d.tw_bound ⌈p⌉₊
  have h2 := mul_le_mul_of_nonneg_right (Nat.le_ceil p) (Nat.cast_nonneg (α := ℝ) (d.tw ⌈p⌉₊))
  linarith

/-- The deterministic entry-fee mechanism on 100 items (entry fee `9`, item price `4`). -/
noncomputable def mech : Mechanism (Fin 100) :=
  (menuMech (α := Fin 100) (β := Fin 0) (fun _ => 4) 9 0).reindex
    (Equiv.sumEmpty (Fin 100) (Fin 0)).symm

theorem mech_det (v : Fin 100 → ℝ) (i : Fin 100) : mech.alloc v i = 0 ∨ mech.alloc v i = 1 := by
  unfold mech Mechanism.reindex
  dsimp only
  exact menuMech_det (α := Fin 100) (β := Fin 0) (fun _ => 4) 9 0 _ _

theorem mech_pay (v : Fin 100 → ℝ) : mech.pay v =
    if (9:ℝ) ≤ ∑ i, max (v i - 4) 0 then 9 + ∑ i, (if (4:ℝ) ≤ v i then (4:ℝ) else 0) else 0 := by
  unfold mech Mechanism.reindex menuMech surplus
  by_cases h : (9:ℝ) ≤ ∑ i, max (v i - 4) 0 <;> simp [h]

theorem rev_ge : (15985442 / 1000000 : ℝ) ≤ mech.rev d.DF := by
  have h : ∀ ω : O, prob d.DF ω * mech.pay (value d.DF ω) =
      ((if 9 ≤ spl ω then d.w2 ω else 0 : ℕ) : ℝ) / d.Dn := by
    intro ω
    have hv : ∀ i, value d.DF ω i = ((ω i : ℕ) : ℝ) := fun _ => rfl
    have hs : ∑ i, max (value d.DF ω i - 4) 0 = (spl ω : ℝ) := by
      rw [spl, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [hv]
      rcases le_total 4 (ω i : ℕ) with h | h
      · rw [Nat.cast_sub h, max_eq_left]
        · norm_num
        · have : (4:ℝ) ≤ ((ω i : ℕ) : ℝ) := by exact_mod_cast h
          linarith
      · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, max_eq_right]
        have : ((ω i : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h
        linarith
    have hp : ∑ i, (if (4:ℝ) ≤ value d.DF ω i then (4:ℝ) else 0) = (py ω : ℝ) := by
      rw [py, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [hv]
      by_cases h : 4 ≤ (ω i : ℕ)
      · rw [if_pos h, if_pos (by exact_mod_cast h)]; norm_num
      · rw [if_neg h, if_neg (by exact_mod_cast h)]; simp
    rw [mech_pay, hs, hp, d.prob_DF]
    by_cases he : 9 ≤ spl ω
    · rw [if_pos he, if_pos (by exact_mod_cast he), w2]
      push_cast; ring
    · rw [if_neg he, if_neg (by exact_mod_cast he), mul_zero, Nat.cast_zero, zero_div]
  have h2 : mech.rev d.DF = ((∑ ω : O, if 9 ≤ spl ω then d.w2 ω else 0 : ℕ) : ℝ) / d.Dn := by
    unfold Mechanism.rev
    rw [Nat.cast_sum, sum_div]
    exact sum_congr rfl fun ω _ => h ω
  rw [h2, div_le_div_iff₀ (by norm_num) d.Dn_posR]
  have hnat : (15985442 : ℝ) * (d.Dn : ℝ) ≤
      (1000000 : ℝ) * ((∑ ω : O, if 9 ≤ spl ω then d.w2 ω else 0 : ℕ) : ℝ) := by
    exact_mod_cast d.rev_nat
  linarith

end IID100Data

namespace IID100Cert

theorem pow9_eq (a : ℕ) : pow9 a = a ^ 9 := by unfold pow9; ring
theorem pow99_eq (a : ℕ) : pow99 a = a ^ 99 := by unfold pow99; ring
theorem pow100_eq (a : ℕ) : pow100 a = a ^ 100 := by unfold pow100; ring

theorem pow99Mod_modEq (M a : ℕ) : pow99Mod M a ≡ a ^ 99 [MOD M] := by
  unfold pow99Mod
  set a1 := a % M
  set a2 := a1 * a1 % M
  set a3 := a2 * a1 % M
  set a4 := a2 * a2 % M
  set a8 := a4 * a4 % M
  set a16 := a8 * a8 % M
  set a32 := a16 * a16 % M
  set a64 := a32 * a32 % M
  have h1 : a1 ≡ a [MOD M] := Nat.mod_modEq a M
  have h2 : a2 ≡ a ^ 2 [MOD M] := by
    rw [sq]; exact (Nat.mod_modEq _ _).trans (h1.mul h1)
  have h3 : a3 ≡ a ^ 3 [MOD M] := by
    rw [show a ^ 3 = a ^ 2 * a by ring]; exact (Nat.mod_modEq _ _).trans (h2.mul h1)
  have h4 : a4 ≡ a ^ 4 [MOD M] := by
    rw [show a ^ 4 = a ^ 2 * a ^ 2 by ring]; exact (Nat.mod_modEq _ _).trans (h2.mul h2)
  have h8 : a8 ≡ a ^ 8 [MOD M] := by
    rw [show a ^ 8 = a ^ 4 * a ^ 4 by ring]; exact (Nat.mod_modEq _ _).trans (h4.mul h4)
  have h16 : a16 ≡ a ^ 16 [MOD M] := by
    rw [show a ^ 16 = a ^ 8 * a ^ 8 by ring]; exact (Nat.mod_modEq _ _).trans (h8.mul h8)
  have h32 : a32 ≡ a ^ 32 [MOD M] := by
    rw [show a ^ 32 = a ^ 16 * a ^ 16 by ring]; exact (Nat.mod_modEq _ _).trans (h16.mul h16)
  have h64 : a64 ≡ a ^ 64 [MOD M] := by
    rw [show a ^ 64 = a ^ 32 * a ^ 32 by ring]; exact (Nat.mod_modEq _ _).trans (h32.mul h32)
  have h96 : a64 * a32 % M ≡ a ^ 96 [MOD M] := by
    rw [show a ^ 96 = a ^ 64 * a ^ 32 by ring]; exact (Nat.mod_modEq _ _).trans (h64.mul h32)
  have h99 : (a64 * a32 % M) * a3 % M ≡ a ^ 99 [MOD M] := by
    rw [show a ^ 99 = a ^ 96 * a ^ 3 by ring]; exact (Nat.mod_modEq _ _).trans (h96.mul h3)
  exact h99

theorem Dn_eq_pow : Dn = W ^ 100 := by unfold Dn; exact pow100_eq W
theorem W99_eq_pow : W99 = W ^ 99 := by unfold W99; exact pow99_eq W
theorem Me_eq_pow : Me = X ^ 9 := by unfold Me; exact pow9_eq X
theorem Fz_eq_pow : Fz = gz ^ 100 := by unfold Fz; exact pow100_eq gz

theorem YwM_eq_mod : YwM = (9 * gw ^ 100 + 100 * (hw * gw ^ 99)) % X ^ 9 := by
  have h99 : gw99M ≡ gw ^ 99 [MOD Me] := by unfold gw99M; exact pow99Mod_modEq Me gw
  have h100 : gw100M ≡ gw ^ 100 [MOD Me] := by
    unfold gw100M
    have := (Nat.mod_modEq _ _).trans (h99.mul_right gw)
    rwa [show gw ^ 99 * gw = gw ^ 100 by ring] at this
  have hhw : hw * gw99M % Me ≡ hw * gw ^ 99 [MOD Me] :=
    (Nat.mod_modEq _ _).trans (h99.mul_left hw)
  have hsum : 9 * gw100M + 100 * (hw * gw99M % Me) ≡ 9 * gw ^ 100 + 100 * (hw * gw ^ 99) [MOD Me] :=
    (h100.mul_left 9).add (hhw.mul_left 100)
  have : YwM = (9 * gw ^ 100 + 100 * (hw * gw ^ 99)) % Me := by
    unfold YwM; exact hsum
  rwa [Me_eq_pow] at this

theorem sumDigits_eq (x : ℕ) (k : ℕ) : ∀ y t : ℕ,
    sumDigits x k (y / x ^ t) = ∑ j ∈ range k, y / x ^ (t + j) % x := by
  induction k with
  | zero => intro y t; simp [sumDigits]
  | succ k ih =>
    intro y t
    rw [sumDigits, Nat.div_div_eq_div_mul, ← pow_succ, ih y (t + 1), sum_range_succ']
    rw [add_zero, add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show t + 1 + j = t + (j + 1) by ring]

theorem qloss_eq_sum : qloss = ∑ j ∈ range 9, YwM / X ^ j % X := by
  have h := sumDigits_eq X 9 YwM 0
  simpa [qloss] using h

theorem sum_c : ∑ k : Fin 14, cN k = W := by unfold W; decide +kernel
theorem sum_cp : ∑ k : Fin 14, cN k * (if 4 ≤ (k : ℕ) then 4 else 0) = 4 * 90090 := by decide +kernel
theorem tail_check : ∀ m : Fin 15, (m : ℕ) * (∑ k : Fin 14, if (m : ℕ) ≤ (k : ℕ) then cN k else 0) ≤ 360360 := by
  decide +kernel
theorem tail_exact : ∀ m : Fin 14, 1 ≤ (m : ℕ) →
    (∑ k : Fin 14, if (m : ℕ) ≤ (k : ℕ) then cN k else 0) * (25 * max (m : ℕ) 4) = 3 * W := by
  unfold W; decide +kernel

theorem sum_cz : ∑ k : Fin 14, cN k * X ^ (k : ℕ) = gz := by
  unfold gz
  generalize X = x
  simp [Fin.sum_univ_succ, cN]
  ring

theorem sum_cw : ∑ k : Fin 14, cN k * X ^ ((k : ℕ) - 4) = gw := by
  unfold gw
  generalize X = x
  simp [Fin.sum_univ_succ, cN]
  ring

theorem sum_ch : ∑ k : Fin 14, cN k * X ^ ((k : ℕ) - 4) * (if 4 ≤ (k : ℕ) then 4 else 0) = hw := by
  unfold hw
  generalize X = x
  simp [Fin.sum_univ_succ, cN]
  ring

theorem bound_X_pow : (9 * W + 400 * 90090) * W ^ 99 < X := by
  rw [← W99_eq_pow]; exact bound_X

theorem brev_ok_fact : loop X Dn 1301 0 0 Fz = true := by
  have h := brevCheck_true
  rw [brevCheck] at h
  exact h

theorem rev_ok_pow :
    15985442 * Dn + 1000000 * qloss ≤ 1000000 * ((9 * W + 400 * 90090) * W ^ 99) := by
  have h := revCheck_true
  rw [revCheck] at h
  have h1 := Nat.le_of_ble_eq_true h
  rwa [W99_eq_pow] at h1

def theIID100Data : IID100Data where
  W := W
  X := X
  Dn := Dn
  gz := gz
  gw := gw
  hw := hw
  Fz := Fz
  YwM := YwM
  qloss := qloss
  cN := cN
  W_pos := W_pos_nat
  W_val := W_val
  Dn_eq := Dn_eq_pow
  Fz_eq := Fz_eq_pow
  YwM_eq := YwM_eq_mod
  qloss_eq := qloss_eq_sum
  sum_c := sum_c
  sum_cz := sum_cz
  sum_cw := sum_cw
  sum_ch := sum_ch
  sum_cp := sum_cp
  tail_check := tail_check
  tail_exact := tail_exact
  Dn_lt_X := Dn_lt_X
  bound_X := bound_X_pow
  brev_ok := brev_ok_fact
  rev_ok := rev_ok_pow

end IID100Cert

/-- **100-item i.i.d. lower bound (Proposition 5).** -/
theorem iid100_lower_bound_proof :
    ∃ F : FinDist,
      (∀ i : Fin F.size, ∃ k : ℕ, F.val i = (k : ℝ)) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 13 → F.tail (k : ℝ) = (3 : ℝ) / (25 * max (k : ℝ) 4)) ∧
      (∀ k : ℕ, 13 < k → F.tail (k : ℝ) = 0) ∧
      ∃ M : Mechanism (Fin 100),
        (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
        (∀ v, M.pay v =
          if (9 : ℝ) ≤ ∑ i : Fin 100, max (v i - 4) 0 then
            9 + ∑ i : Fin 100, if (4 : ℝ) ≤ v i then (4 : ℝ) else 0
          else 0) ∧
        0 < max (SREV fun _ : Fin 100 => F) (BREV fun _ : Fin 100 => F) ∧
        (1.324907 : ℝ) ≤
          M.rev (fun _ : Fin 100 => F) /
            max (SREV fun _ : Fin 100 => F) (BREV fun _ : Fin 100 => F) ∧
        (1.324907 : ℝ) ≤
          REV (fun _ : Fin 100 => F) /
            max (SREV fun _ : Fin 100 => F) (BREV fun _ : Fin 100 => F) := by
  let d := IID100Cert.theIID100Data
  refine ⟨d.F, fun i => ⟨i.1, rfl⟩, fun k h1 h13 => d.F_tail_eq k h1 h13,
    fun k h13 => d.F_tail_gt13 k h13, IID100Data.mech, IID100Data.mech_det,
    IID100Data.mech_pay, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le d.SREV_pos (le_max_left _ _)
  · have hpos : 0 < max (SREV fun _ : Fin 100 => d.F) (BREV fun _ : Fin 100 => d.F) :=
      lt_of_lt_of_le d.SREV_pos (le_max_left _ _)
    have hmax : max (SREV fun _ : Fin 100 => d.F) (BREV fun _ : Fin 100 => d.F) ≤
        12065329 / 1000000 :=
      max_le (d.SREV_le.trans (by norm_num)) d.BREV_le'
    have hrev : (15985442 / 1000000 : ℝ) ≤ IID100Data.mech.rev (fun _ : Fin 100 => d.F) := d.rev_ge
    rw [le_div_iff₀ hpos]
    nlinarith
  · have hpos : 0 < max (SREV fun _ : Fin 100 => d.F) (BREV fun _ : Fin 100 => d.F) :=
      lt_of_lt_of_le d.SREV_pos (le_max_left _ _)
    have hmax : max (SREV fun _ : Fin 100 => d.F) (BREV fun _ : Fin 100 => d.F) ≤
        12065329 / 1000000 :=
      max_le (d.SREV_le.trans (by norm_num)) d.BREV_le'
    have hrev : (15985442 / 1000000 : ℝ) ≤ REV (fun _ : Fin 100 => d.F) :=
      d.rev_ge.trans (le_REV _ IID100Data.mech)
    rw [le_div_iff₀ hpos]
    nlinarith

end Sievert26SimpleAuctions
