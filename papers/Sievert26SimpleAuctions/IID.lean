import Sievert26SimpleAuctions.Main
import Sievert26SimpleAuctions.Expect
import Sievert26SimpleAuctions.IIDKernel

/-!
# Lower bound for iid items

40 iid items, `Pr[X ≥ k] = 3/(10·max(k,4))` for `1 ≤ k ≤ 13` (equal revenue on `[4,13]`).
Entry fee `9`, then price `4` per item, earns more than `1.316 · max(SREV, BREV)`.

All reasoning is carried out over an abstract `IIDData` record so that Lean never reduces
the large packed integers (`W^40`, `gz^40`, `YwM`) during elaboration.
-/
set_option linter.deprecated false
open Finset

namespace Sievert26SimpleAuctions

/-- Abstract record of all numerical facts for the 40-item iid instance. -/
structure IIDData where
  (W X Dn gz gw hw Fz YwM qloss : ℕ)
  (cN : ℕ → ℕ)
  W_pos : 0 < W
  W_val : 10 * 1081080 = 3 * W
  Dn_eq : Dn = W ^ 40
  Fz_eq : Fz = gz ^ 40
  YwM_eq : YwM = (9 * gw ^ 40 + 40 * (hw * gw ^ 39)) % X ^ 9
  qloss_eq : qloss = ∑ j ∈ range 9, YwM / X ^ j % X
  sum_c : ∑ k : Fin 14, cN k = W
  sum_cz : ∑ k : Fin 14, cN k * X ^ (k : ℕ) = gz
  sum_cw : ∑ k : Fin 14, cN k * X ^ ((k : ℕ) - 4) = gw
  sum_ch : ∑ k : Fin 14, cN k * X ^ ((k : ℕ) - 4) * (if 4 ≤ (k : ℕ) then 4 else 0) = hw
  sum_cp : ∑ k : Fin 14, cN k * (if 4 ≤ (k : ℕ) then 4 else 0) = 4 * 270270
  tail_check : ∀ m : Fin 15, (m : ℕ) * (∑ k : Fin 14, if (m : ℕ) ≤ (k : ℕ) then cN k else 0) ≤ 1081080
  Dn_lt_X : Dn < X
  bound_X : (9 * W + 160 * 270270) * W ^ 39 < X
  brev_ok : IIDCert.loop X Dn 521 0 0 Fz = true
  rev_ok : 16 * Dn + qloss ≤ (9 * W + 160 * 270270) * W ^ 39

namespace IIDData
variable (d : IIDData)

abbrev O : Type := Fin 40 → Fin 14

def wt (ω : O) : ℕ := ∏ i, d.cN (ω i)
def zz (ω : O) : ℕ := ∑ i, (ω i : ℕ)
def spl (ω : O) : ℕ := ∑ i, ((ω i : ℕ) - 4)
def py (ω : O) : ℕ := ∑ i, if 4 ≤ (ω i : ℕ) then 4 else 0

theorem sum_wt : ∑ ω, d.wt ω = d.Dn := by
  unfold wt
  rw [sum_prod_pi (fun (_ : Fin 40) (k : Fin 14) => d.cN k)]
  simp only [d.sum_c, prod_const, card_univ, Fintype.card_fin, d.Dn_eq]

theorem gen_z : ∑ ω, d.wt ω * d.X ^ zz ω = d.Fz := by
  have h1 : ∀ ω : O, d.wt ω * d.X ^ zz ω = ∏ i, (d.cN (ω i) * d.X ^ (ω i : ℕ)) := by
    intro ω; rw [wt, zz, prod_mul_distrib, prod_pow_eq_pow_sum]
  simp_rw [h1]
  rw [sum_prod_pi (fun (_ : Fin 40) (k : Fin 14) => d.cN k * d.X ^ (k : ℕ))]
  simp only [d.sum_cz, prod_const, card_univ, Fintype.card_fin, d.Fz_eq]

def a (t : ℕ) : ℕ := ∑ ω, if zz ω = t then d.wt ω else 0

theorem digit_a (t : ℕ) : d.Fz / d.X ^ t % d.X = d.a t := by
  rw [← d.gen_z]
  exact Cert.digit_sum d.wt zz d.X (by rw [d.sum_wt]; exact d.Dn_lt_X) t

theorem loop_sound (F : ℕ) (b : ℕ → ℕ) (hF : ∀ t, F / d.X ^ t % d.X = b t) (f : ℕ) : ∀ t,
    IIDCert.loop d.X d.Dn f t (∑ i ∈ range t, b i) (F / d.X ^ t) = true →
    ∀ j < f, (t + j) * (d.Dn - ∑ i ∈ range (t + j), b i) * 1000 ≤ 12151 * d.Dn := by
  induction f with
  | zero => intro t _ j hj; omega
  | succ f ih =>
    intro t h j hj
    rw [IIDCert.loop, Bool.and_eq_true] at h
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

theorem zz_le (ω : O) : zz ω ≤ 520 := by
  unfold zz
  calc ∑ i, (ω i : ℕ) ≤ ∑ _i : Fin 40, 13 := sum_le_sum fun i _ => by have := (ω i).isLt; omega
    _ = 520 := by simp

theorem tw_bound (t : ℕ) : t * d.tw t * 1000 ≤ 12151 * d.Dn := by
  by_cases ht : t ≤ 520
  · have h := d.loop_sound d.Fz d.a d.digit_a 521 0
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

theorem gen_w : ∑ ω, d.wt ω * d.X ^ spl ω = d.gw ^ 40 := by
  simp_rw [d.wt_spl]
  rw [sum_prod_pi (fun (_ : Fin 40) (k : Fin 14) => d.cN k * d.X ^ ((k : ℕ) - 4))]
  simp only [d.sum_cw, prod_const, card_univ, Fintype.card_fin]

theorem gen_p (i : Fin 40) : ∑ ω, (d.wt ω * d.X ^ spl ω) * (if 4 ≤ (ω i : ℕ) then 4 else 0) =
    d.hw * d.gw ^ 39 := by
  simp_rw [d.wt_spl]
  have h := sum_prod_marg (fun _ : Fin 40 => 14) (fun _ k => d.cN k * d.X ^ (k - 4))
    (fun k => if 4 ≤ k then 4 else 0) i
  rw [h]
  simp only [d.sum_cw, d.sum_ch, prod_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]

theorem gen_y : ∑ ω, d.w2 ω * d.X ^ spl ω = 9 * d.gw ^ 40 + 40 * (d.hw * d.gw ^ 39) := by
  have h1 : ∀ ω : O, d.w2 ω * d.X ^ spl ω = 9 * (d.wt ω * d.X ^ spl ω) +
      ∑ i, (d.wt ω * d.X ^ spl ω) * (if 4 ≤ (ω i : ℕ) then 4 else 0) := by
    intro ω; rw [w2, py, ← mul_sum]; ring
  simp_rw [h1]
  rw [sum_add_distrib, ← mul_sum, d.gen_w, sum_comm]
  simp_rw [d.gen_p]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem sum_w2 : ∑ ω, d.w2 ω = (9 * d.W + 160 * 270270) * d.W ^ 39 := by
  have h1 : ∀ ω : O, d.w2 ω = 9 * d.wt ω + ∑ i, d.wt ω * (if 4 ≤ (ω i : ℕ) then 4 else 0) := by
    intro ω; rw [w2, py, ← mul_sum]; ring
  have h2 : ∀ i : Fin 40, ∑ ω, d.wt ω * (if 4 ≤ (ω i : ℕ) then 4 else 0) =
      4 * 270270 * d.W ^ 39 := by
    intro i
    unfold wt
    have h := sum_prod_marg (fun _ : Fin 40 => 14) (fun _ k => d.cN k)
      (fun k => if 4 ≤ k then 4 else 0) i
    rw [h]
    simp only [d.sum_c, d.sum_cp, prod_const, card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin]
  simp_rw [h1]
  rw [sum_add_distrib, ← mul_sum, d.sum_wt, sum_comm]
  simp_rw [h2]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, d.Dn_eq,
    show (40 : ℕ) = 39 + 1 from rfl, pow_succ]
  ring

theorem digit_y (j : ℕ) (hj : j < 9) : d.YwM / d.X ^ j % d.X = ∑ ω, if spl ω = j then d.w2 ω else 0 := by
  rw [d.YwM_eq, Cert.mod_digit _ _ _ _ hj, ← d.gen_y]
  exact Cert.digit_sum d.w2 spl d.X (by rw [d.sum_w2]; exact d.bound_X) j

theorem rev_nat : 16 * d.Dn ≤ ∑ ω, if 9 ≤ spl ω then d.w2 ω else 0 := by
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

/-- the common item distribution -/
noncomputable def F : FinDist where
  size := 14
  val k := ((k : ℕ) : ℝ)
  prob k := (d.cN k : ℝ) / d.W
  val_nonneg k := Nat.cast_nonneg _
  prob_nonneg k := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  prob_sum := by
    rw [← sum_div, div_eq_one_iff_eq d.W_posR.ne', ← Nat.cast_sum, d.sum_c]

noncomputable def DF (_ : Fin 40) : FinDist := d.F

theorem prob_DF (ω : O) : prob d.DF ω = (d.wt ω : ℝ) / d.Dn := by
  change ∏ i : Fin 40, ((d.cN (ω i) : ℝ) / d.W) = _
  rw [prod_div_distrib, prod_const, wt, Nat.cast_prod, d.Dn_eq, Nat.cast_pow]
  simp

theorem F_rev : d.F.rev ≤ 3 / 10 := by
  refine FinDist.rev_le _ _ fun p hp => ?_
  have h : d.F.tail p = ((∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0 : ℕ) : ℝ) / d.W := by
    rw [Nat.cast_sum, sum_div]
    change ∑ k : Fin 14, (if p ≤ ((k : ℕ) : ℝ) then (d.cN k : ℝ) / d.W else 0) = _
    refine sum_congr rfl fun k _ => ?_
    by_cases h : p ≤ ((k : ℕ) : ℝ)
    · rw [if_pos h, if_pos (Nat.ceil_le.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (Nat.ceil_le.mp hh))]; simp
  have hm : ⌈p⌉₊ * (∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0) ≤ 1081080 := by
    by_cases hlt : ⌈p⌉₊ < 15
    · exact d.tail_check ⟨⌈p⌉₊, hlt⟩
    · have : (∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0) = 0 :=
        sum_eq_zero fun k _ => by rw [if_neg (by have := k.isLt; omega)]
      rw [this]; simp
  rw [h, ← mul_div_assoc, div_le_iff₀ d.W_posR]
  have h3 : (⌈p⌉₊ : ℝ) * ((∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0 : ℕ) : ℝ) ≤ 1081080 := by
    exact_mod_cast hm
  have h4 := mul_le_mul_of_nonneg_right (Nat.le_ceil p)
    (Nat.cast_nonneg (α := ℝ) (∑ k : Fin 14, if ⌈p⌉₊ ≤ (k : ℕ) then d.cN k else 0))
  have h5 : (10 * 1081080 : ℝ) = 3 * (d.W : ℝ) := by exact_mod_cast d.W_val
  linarith

theorem SREV_le : SREV d.DF ≤ 12 := by
  calc SREV d.DF ≤ ∑ _i : Fin 40, (3 / 10 : ℝ) := sum_le_sum fun _ _ => d.F_rev
    _ = 12 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num

theorem BREV_le' : BREV d.DF ≤ 12.151 := by
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
  have h1 : (⌈p⌉₊ : ℝ) * (d.tw ⌈p⌉₊ : ℝ) * 1000 ≤ 12151 * d.Dn := by exact_mod_cast d.tw_bound ⌈p⌉₊
  have h2 := mul_le_mul_of_nonneg_right (Nat.le_ceil p) (Nat.cast_nonneg (α := ℝ) (d.tw ⌈p⌉₊))
  have h3 : (12.151 : ℝ) = 12151 / 1000 := by norm_num
  rw [h3]; linarith

/-- the entry-fee mechanism on 40 items -/
noncomputable def mech : Mechanism (Fin 40) :=
  (menuMech (α := Fin 40) (β := Fin 0) (fun _ => 4) 9 0).reindex (Equiv.sumEmpty (Fin 40) (Fin 0)).symm

theorem mech_det (v : Fin 40 → ℝ) (i : Fin 40) : mech.alloc v i = 0 ∨ mech.alloc v i = 1 := by
  unfold mech Mechanism.reindex
  dsimp only
  exact menuMech_det (α := Fin 40) (β := Fin 0) (fun _ => 4) 9 0 _ _

theorem mech_pay (v : Fin 40 → ℝ) : mech.pay v =
    if (9:ℝ) ≤ ∑ i, max (v i - 4) 0 then 9 + ∑ i, (if (4:ℝ) ≤ v i then (4:ℝ) else 0) else 0 := by
  unfold mech Mechanism.reindex menuMech surplus
  by_cases h : (9:ℝ) ≤ ∑ i, max (v i - 4) 0 <;> simp [h]

theorem rev_ge : 16 ≤ mech.rev d.DF := by
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
  rw [h2, le_div_iff₀ d.Dn_posR]
  exact_mod_cast d.rev_nat

include d in
theorem lower_bound_with_mech_of_data :
    ∃ F : FinDist,
      (1.316 : ℝ) * max (SREV fun _ : Fin 40 => F) (BREV fun _ : Fin 40 => F) <
        REV (fun _ : Fin 40 => F) ∧
      ∃ M : Mechanism (Fin 40),
        (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
        (∀ v, M.pay v =
          if (9 : ℝ) ≤ ∑ i : Fin 40, max (v i - 4) 0 then
            9 + ∑ i : Fin 40, if (4 : ℝ) ≤ v i then (4 : ℝ) else 0
          else 0) ∧
        (1.316 : ℝ) * max (SREV fun _ : Fin 40 => F) (BREV fun _ : Fin 40 => F) <
          M.rev (fun _ : Fin 40 => F) := by
  refine ⟨d.F, ?_, mech, mech_det, mech_pay, ?_⟩
  · have h1 : SREV (fun _ : Fin 40 => d.F) ≤ 12 := d.SREV_le
    have h2 : BREV (fun _ : Fin 40 => d.F) ≤ 12.151 := d.BREV_le'
    have h3 : 16 ≤ REV (fun _ : Fin 40 => d.F) := d.rev_ge.trans (le_REV _ mech)
    have h4 : max (SREV fun _ : Fin 40 => d.F) (BREV fun _ : Fin 40 => d.F) ≤ 12.151 :=
      max_le (by linarith) h2
    linarith
  · have h1 : SREV (fun _ : Fin 40 => d.F) ≤ 12 := d.SREV_le
    have h2 : BREV (fun _ : Fin 40 => d.F) ≤ 12.151 := d.BREV_le'
    have h3 : 16 ≤ mech.rev (fun _ : Fin 40 => d.F) := d.rev_ge
    have h4 : max (SREV fun _ : Fin 40 => d.F) (BREV fun _ : Fin 40 => d.F) ≤ 12.151 :=
      max_le (by linarith) h2
    linarith

include d in
theorem lower_bound_of_data :
    ∃ (m : ℕ) (F : FinDist),
      (1.316 : ℝ) * max (SREV fun _ : Fin m => F) (BREV fun _ : Fin m => F) <
        REV fun _ : Fin m => F := by
  obtain ⟨F, h, _⟩ := d.lower_bound_with_mech_of_data
  exact ⟨40, F, h⟩

end IIDData

namespace IIDCert

theorem pow9_eq (a : ℕ) : pow9 a = a ^ 9 := by unfold pow9; ring
theorem pow39_eq (a : ℕ) : pow39 a = a ^ 39 := by unfold pow39; ring
theorem pow40_eq (a : ℕ) : pow40 a = a ^ 40 := by unfold pow40; ring

theorem pow39Mod_modEq (M a : ℕ) : pow39Mod M a ≡ a ^ 39 [MOD M] := by
  unfold pow39Mod
  dsimp only
  have h1 : a % M ≡ a [MOD M] := Nat.mod_modEq a M
  have h2 : a % M * (a % M) % M ≡ a ^ 2 [MOD M] := by
    rw [sq]; exact (Nat.mod_modEq _ _).trans (h1.mul h1)
  have h3 : a % M * (a % M) % M * (a % M) % M ≡ a ^ 3 [MOD M] := by
    rw [show a ^ 3 = a ^ 2 * a by ring]; exact (Nat.mod_modEq _ _).trans (h2.mul h1)
  have h4 : a % M * (a % M) % M * (a % M * (a % M) % M) % M ≡ a ^ 4 [MOD M] := by
    rw [show a ^ 4 = a ^ 2 * a ^ 2 by ring]; exact (Nat.mod_modEq _ _).trans (h2.mul h2)
  have h7 : a % M * (a % M) % M * (a % M * (a % M) % M) % M *
      (a % M * (a % M) % M * (a % M) % M) % M ≡ a ^ 7 [MOD M] := by
    rw [show a ^ 7 = a ^ 4 * a ^ 3 by ring]; exact (Nat.mod_modEq _ _).trans (h4.mul h3)
  have h8 : a % M * (a % M) % M * (a % M * (a % M) % M) % M *
      (a % M * (a % M) % M * (a % M * (a % M) % M) % M) % M ≡ a ^ 8 [MOD M] := by
    rw [show a ^ 8 = a ^ 4 * a ^ 4 by ring]; exact (Nat.mod_modEq _ _).trans (h4.mul h4)
  have h16 : (a % M * (a % M) % M * (a % M * (a % M) % M) % M *
      (a % M * (a % M) % M * (a % M * (a % M) % M) % M) % M) *
      (a % M * (a % M) % M * (a % M * (a % M) % M) % M *
      (a % M * (a % M) % M * (a % M * (a % M) % M) % M) % M) % M ≡ a ^ 16 [MOD M] := by
    rw [show a ^ 16 = a ^ 8 * a ^ 8 by ring]; exact (Nat.mod_modEq _ _).trans (h8.mul h8)
  have h32 := (Nat.mod_modEq _ _).trans (h16.mul h16)
  rw [show a ^ 16 * a ^ 16 = a ^ 32 by ring] at h32
  have h39 := (Nat.mod_modEq _ _).trans (h32.mul h7)
  rwa [show a ^ 32 * a ^ 7 = a ^ 39 by ring] at h39

theorem Dn_eq_pow : Dn = W ^ 40 := by unfold Dn; exact pow40_eq W
theorem W39_eq_pow : W39 = W ^ 39 := by unfold W39; exact pow39_eq W
theorem Me_eq_pow : Me = X ^ 9 := by unfold Me; exact pow9_eq X
theorem Fz_eq_pow : Fz = gz ^ 40 := by unfold Fz; exact pow40_eq gz

theorem YwM_eq_mod : YwM = (9 * gw ^ 40 + 40 * (hw * gw ^ 39)) % X ^ 9 := by
  have h39 : gw39M ≡ gw ^ 39 [MOD Me] := by unfold gw39M; exact pow39Mod_modEq Me gw
  have h40 : gw40M ≡ gw ^ 40 [MOD Me] := by
    unfold gw40M
    have := (Nat.mod_modEq _ _).trans (h39.mul_right gw)
    rwa [show gw ^ 39 * gw = gw ^ 40 by ring] at this
  have hhw : hw * gw39M % Me ≡ hw * gw ^ 39 [MOD Me] :=
    (Nat.mod_modEq _ _).trans (h39.mul_left hw)
  have hsum : 9 * gw40M + 40 * (hw * gw39M % Me) ≡ 9 * gw ^ 40 + 40 * (hw * gw ^ 39) [MOD Me] :=
    (h40.mul_left 9).add (hhw.mul_left 40)
  have : YwM = (9 * gw ^ 40 + 40 * (hw * gw ^ 39)) % Me := by
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
theorem sum_cp : ∑ k : Fin 14, cN k * (if 4 ≤ (k : ℕ) then 4 else 0) = 4 * 270270 := by decide +kernel
theorem tail_check : ∀ m : Fin 15, (m : ℕ) * (∑ k : Fin 14, if (m : ℕ) ≤ (k : ℕ) then cN k else 0) ≤ 1081080 := by
  decide +kernel

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

theorem bound_X_pow : (9 * W + 160 * 270270) * W ^ 39 < X := by
  rw [← W39_eq_pow]; exact bound_X

theorem brev_ok_fact : loop X Dn 521 0 0 Fz = true := by
  have h := brevCheck_true
  rw [brevCheck] at h
  exact h

theorem rev_ok_pow : 16 * Dn + qloss ≤ (9 * W + 160 * 270270) * W ^ 39 := by
  have h := revCheck_true
  rw [revCheck] at h
  have h1 := Nat.le_of_ble_eq_true h
  rwa [W39_eq_pow] at h1

/-- Concrete instantiation of the 40-item iid instance. -/
def theIIDData : IIDData where
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
  Dn_lt_X := Dn_lt_X
  bound_X := bound_X_pow
  brev_ok := brev_ok_fact
  rev_ok := rev_ok_pow

end IIDCert

theorem iid_lower_bound_with_mech :
    ∃ F : FinDist,
      (1.316 : ℝ) * max (SREV fun _ : Fin 40 => F) (BREV fun _ : Fin 40 => F) <
        REV (fun _ : Fin 40 => F) ∧
      ∃ M : Mechanism (Fin 40),
        (∀ v i, M.alloc v i = 0 ∨ M.alloc v i = 1) ∧
        (∀ v, M.pay v =
          if (9 : ℝ) ≤ ∑ i : Fin 40, max (v i - 4) 0 then
            9 + ∑ i : Fin 40, if (4 : ℝ) ≤ v i then (4 : ℝ) else 0
          else 0) ∧
        (1.316 : ℝ) * max (SREV fun _ : Fin 40 => F) (BREV fun _ : Fin 40 => F) <
          M.rev (fun _ : Fin 40 => F) :=
  IIDCert.theIIDData.lower_bound_with_mech_of_data

/-- **iid lower bound.** Forty iid items with optimal revenue strictly above `1.316 · max(SREV, BREV)`
(improving the previously cited `1.1877` lower bound by more than `+0.128`). -/
theorem iid_lower_bound : ∃ (m : ℕ) (F : FinDist),
    (1.316 : ℝ) * max (SREV fun _ : Fin m => F) (BREV fun _ : Fin m => F) <
      REV fun _ : Fin m => F :=
  IIDCert.theIIDData.lower_bound_of_data

end Sievert26SimpleAuctions
