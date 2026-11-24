import Sievert26SimpleAuctions.Basic
import Sievert26SimpleAuctions.Spec

/-!
The finite group `A` (5 types, 256 iid copies each), analysed *abstractly*: every numerical fact
is a field of `Data`, so that the huge constants are never unfolded here.
-/
set_option linter.deprecated false
open Finset

namespace Sievert26SimpleAuctions

section marginals
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Type*} [CommSemiring S]

/-- `E[Π u_j · f(ω_i)]` factorises. -/
theorem sum_prod_marg (κ : ι → ℕ) (u : ι → ℕ → S) (f : ℕ → S) (i : ι) :
    ∑ ω : ((i : ι) → Fin (κ i)), (∏ j, u j (ω j)) * f (ω i) =
    (∑ k : Fin (κ i), u i k * f k) * ∏ j ∈ univ.erase i, ∑ k : Fin (κ j), u j k := by
  have h1 : ∀ ω : ((i : ι) → Fin (κ i)), (∏ j, u j (ω j)) * f (ω i) =
      ∏ j, (u j (ω j) * if j = i then f (ω j) else 1) := by
    intro ω
    rw [prod_mul_distrib, prod_ite_eq' univ i]
    simp
  simp_rw [h1]
  rw [sum_prod_pi (fun j (k : Fin (κ j)) => u j k * if j = i then f k else 1),
    ← mul_prod_erase univ _ (mem_univ i)]
  simp only [if_true]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  simp only [if_neg (ne_of_mem_erase hj), mul_one]

end marginals

open Cert (digit_sum mod_digit yfull Cs Ss)

/-- All numerical facts needed about group `A` (abstract, so that nothing gets evaluated). -/
structure Data where
  (N e T X W Dn EZ Epay : ℕ)
  (P R : Fin 5 → ℕ)
  (cf : Fin 5 → ℕ → ℕ)
  (gA gW hW mean pay : Fin 5 → ℕ)
  (dF dY : ℕ → ℕ)
  N_pos : 0 < N
  e_pos : 0 < e
  tail_le : ∀ i m n, m * ∑ k ∈ range n, (if m ≤ k then cf i k else 0) ≤ R i
  R_sum : 256 * (R 0 + R 1 + R 2 + R 3 + R 4) ≤ N * W
  W_gt : 1 < W
  Dn_eq : Dn = W ^ 1280
  X_eq : X = Dn * W
  sum_cf : ∀ i, ∑ k ∈ range (P i + e + 1), cf i k = W
  gA_eq : ∀ i, gA i = ∑ k ∈ range (P i + e + 1), cf i k * X ^ k
  mean_eq : ∀ i, mean i = ∑ k ∈ range (P i + e + 1), cf i k * k
  gW_eq : ∀ i, gW i = ∑ k ∈ range (P i + e + 1), cf i k * X ^ (k - P i)
  hW_eq : ∀ i, hW i =
    ∑ k ∈ range (P i + e + 1), cf i k * X ^ (k - P i) * (if P i ≤ k then P i else 0)
  pay_eq : ∀ i, ∑ k ∈ range (P i + e + 1), cf i k * (if P i ≤ k then P i else 0) = pay i
  EZ_eq : EZ = 256 * (mean 0 + mean 1 + mean 2 + mean 3 + mean 4)
  Epay_eq : Epay = e * W + 256 * (pay 0 + pay 1 + pay 2 + pay 3 + pay 4)
  Epay_lt : Epay < W * W
  dF_eq : ∀ t < T, dF t = (∏ i : Fin 5, gA i ^ 256) / X ^ t % X
  dY_eq : ∀ j < e, dY j = yfull e gW hW / X ^ j % X
  check : ∀ t, 0 < t → t ≤ T → (N + t) * (Dn - Cs dF t) ≤ N * Dn
  final : EZ * Dn + W * Ss dF T ≤ W * ((N + T) * Cs dF T)
  rev : 100000 * (W * ∑ j ∈ range e, dY j) + 119464 * (N * (W * Dn)) ≤ 100000 * (Epay * Dn)

namespace Data
variable (d : Data)

abbrev IA : Type := Fin 5 × Fin 256
abbrev kap (i : IA) : ℕ := d.P i.1 + d.e + 1
abbrev OA : Type := (i : IA) → Fin (d.kap i)

/-- integer weight of a realisation -/
def w (ω : d.OA) : ℕ := ∏ i : IA, d.cf i.1 (ω i)
/-- total value -/
def z (ω : d.OA) : ℕ := ∑ i : IA, (ω i : ℕ)
/-- total surplus at item prices -/
def sp (ω : d.OA) : ℕ := ∑ i : IA, ((ω i : ℕ) - d.P i.1)
/-- item payments -/
def py (ω : d.OA) : ℕ := ∑ i : IA, if d.P i.1 ≤ (ω i : ℕ) then d.P i.1 else 0

theorem W_pos : 0 < d.W := by have := d.W_gt; omega
set_option exponentiation.threshold 2048 in
theorem Dn_pos : 0 < d.Dn := by rw [d.Dn_eq]; exact Nat.pow_pos d.W_pos
theorem X_pos : 0 < d.X := by rw [d.X_eq]; exact Nat.mul_pos d.Dn_pos d.W_pos

theorem sum_cf_fin (i : IA) : ∑ k : Fin (d.kap i), d.cf i.1 k = d.W := by
  rw [Fin.sum_univ_eq_sum_range (fun k => d.cf i.1 k)]
  exact d.sum_cf _

theorem sum_w : ∑ ω, d.w ω = d.Dn := by
  unfold w
  rw [sum_prod_pi (fun i (k : Fin (d.kap i)) => d.cf i.1 k)]
  simp_rw [sum_cf_fin]
  rw [prod_const, d.Dn_eq]
  simp

theorem sum_w_lt : ∑ ω, d.w ω < d.X := by
  rw [sum_w, d.X_eq]
  exact lt_mul_of_one_lt_right d.Dn_pos d.W_gt

theorem genA : ∑ ω, d.w ω * d.X ^ d.z ω = ∏ i : Fin 5, d.gA i ^ 256 := by
  have h1 : ∀ ω : d.OA, d.w ω * d.X ^ d.z ω = ∏ i : IA, (d.cf i.1 (ω i) * d.X ^ (ω i : ℕ)) := by
    intro ω; rw [w, z, prod_mul_distrib, prod_pow_eq_pow_sum]
  simp_rw [h1]
  rw [sum_prod_pi (fun (i : IA) (k : Fin (d.kap i)) => d.cf i.1 k * d.X ^ (k : ℕ)),
    Fintype.prod_prod_type]
  refine prod_congr rfl fun τ _ => ?_
  have h2 : ∀ c : Fin 256, ∑ k : Fin (d.kap (τ, c)), d.cf τ k * d.X ^ (k : ℕ) = d.gA τ := by
    intro c
    rw [d.gA_eq, Fin.sum_univ_eq_sum_range (fun k => d.cf τ k * d.X ^ k)]
  rw [prod_congr rfl (fun c _ => h2 c), prod_const]
  simp

/-- weight of `{Z = t}` -/
def aA (t : ℕ) : ℕ := ∑ ω, if d.z ω = t then d.w ω else 0

theorem dF_aA (t : ℕ) (ht : t < d.T) : d.dF t = d.aA t := by
  rw [d.dF_eq t ht, ← genA]
  exact digit_sum d.w d.z d.X d.sum_w_lt t

theorem Cs_dF (t : ℕ) (ht : t ≤ d.T) : Cs d.dF t = Cs d.aA t :=
  sum_congr rfl fun i hi => d.dF_aA i (lt_of_lt_of_le (mem_range.mp hi) ht)

theorem Ss_dF (t : ℕ) (ht : t ≤ d.T) : Ss d.dF t = Ss d.aA t :=
  sum_congr rfl fun i hi => d.Cs_dF (i+1) (by have := mem_range.mp hi; omega)

theorem Cs_aA (t : ℕ) : Cs d.aA t = ∑ ω, if d.z ω < t then d.w ω else 0 := by
  unfold Cs aA
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [sum_ite_eq (range t) (d.z ω) (fun _ => d.w ω)]
  simp

/-- weight of `{Z ≥ t}` -/
def tw (t : ℕ) : ℕ := ∑ ω, if t ≤ d.z ω then d.w ω else 0

theorem tw_add (t : ℕ) : d.tw t + Cs d.aA t = d.Dn := by
  rw [Cs_aA, tw, ← sum_add_distrib, ← sum_w]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : t ≤ d.z ω
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega), zero_add]

theorem card_aux (z t : ℕ) : (∑ i ∈ range t, if z < i + 1 then 1 else 0) = t - z := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, ih]; split_ifs <;> omega

theorem Ss_aA (t : ℕ) : Ss d.aA t = ∑ ω, d.w ω * (t - d.z ω) := by
  unfold Ss
  simp_rw [Cs_aA]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [← card_aux, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem marg_w (f : ℕ → ℕ) (i : IA) :
    (∑ ω : d.OA, d.w ω * f (ω i)) * d.W =
      (∑ k ∈ range (d.kap i), d.cf i.1 k * f k) * d.Dn := by
  unfold w
  have h := sum_prod_marg d.kap (fun (j : IA) k => d.cf j.1 k) f i
  rw [h, Fin.sum_univ_eq_sum_range (fun k => d.cf i.1 k * f k), mul_assoc]
  congr 1
  simp_rw [sum_cf_fin]
  rw [prod_erase_mul univ (fun _ : IA => d.W) (mem_univ i), prod_const, d.Dn_eq]
  simp

theorem sum_wz : (∑ ω, d.w ω * d.z ω) * d.W = d.EZ * d.Dn := by
  unfold z
  simp_rw [mul_sum]
  rw [sum_comm, sum_mul]
  have h : ∀ i : IA, (∑ ω : d.OA, d.w ω * (ω i : ℕ)) * d.W = d.mean i.1 * d.Dn := by
    intro i
    rw [d.mean_eq]
    exact d.marg_w (fun k => k) i
  rw [sum_congr rfl (fun i _ => h i), ← sum_mul, Fintype.sum_prod_type]
  refine congrArg (· * d.Dn) ?_
  rw [Fin.sum_univ_five, d.EZ_eq]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem pointwise_aux (N T t z w : ℕ) (ht : T < t) :
    (N + t) * (if t ≤ z then w else 0) + (N + T) * (if z < T then w else 0) ≤
      N * w + (w * z + w * (T - z)) := by
  by_cases ha : t ≤ z
  · rw [if_pos ha, if_neg (by omega), Nat.sub_eq_zero_of_le (by omega)]
    have : t * w ≤ z * w := Nat.mul_le_mul_right _ ha
    nlinarith
  · rw [if_neg ha]
    by_cases hb : z < T
    · rw [if_pos hb]
      obtain ⟨u, rfl⟩ : ∃ u, T = z + u := ⟨T - z, by omega⟩
      rw [Nat.add_sub_cancel_left]
      apply le_of_eq; ring
    · rw [if_neg hb]; simp

/-- integer form of the grand-bundle bound: `(N+t) Pr[Z ≥ t] ≤ N` for all `t`. -/
theorem tw_bound (t : ℕ) : (d.N + t) * d.tw t ≤ d.N * d.Dn := by
  have h3 := d.tw_add t
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    rw [add_zero]
    exact Nat.mul_le_mul_left _ (by omega)
  by_cases hT : t ≤ d.T
  · have := d.check t h0 hT
    rw [d.Cs_dF t hT] at this
    rwa [show d.Dn - Cs d.aA t = d.tw t by omega] at this
  · have h4 := d.final
    rw [d.Cs_dF _ le_rfl, d.Ss_dF _ le_rfl, ← sum_wz, mul_comm _ d.W, ← mul_add] at h4
    have h5 : ∑ ω, d.w ω * d.z ω + Ss d.aA d.T ≤ (d.N + d.T) * Cs d.aA d.T :=
      Nat.le_of_mul_le_mul_left h4 d.W_pos
    have h6 : (d.N + t) * d.tw t + ((d.N + d.T) * Cs d.aA d.T) ≤
        d.N * d.Dn + (∑ ω, d.w ω * d.z ω + Ss d.aA d.T) := by
      rw [Cs_aA, Ss_aA, tw, ← sum_w, mul_sum, mul_sum, mul_sum, ← sum_add_distrib,
        ← sum_add_distrib, ← sum_add_distrib]
      exact sum_le_sum fun ω _ => pointwise_aux d.N d.T t (d.z ω) (d.w ω) (not_le.mp hT)
    omega

/-! ### Revenue of the entry-fee mechanism -/

/-- weight times payment (if entering) -/
def w2 (ω : d.OA) : ℕ := d.w ω * (d.e + d.py ω)

theorem gW_pos (τ : Fin 5) : 0 < d.gW τ := by
  rw [d.gW_eq]
  refine lt_of_lt_of_le d.W_pos ?_
  rw [← d.sum_cf τ]
  exact sum_le_sum fun k _ => Nat.le_mul_of_pos_right _ (Nat.pow_pos d.X_pos)

theorem prod_all_gW : ∏ j : IA, d.gW j.1 =
    d.gW 0 ^ 256 * d.gW 1 ^ 256 * d.gW 2 ^ 256 * d.gW 3 ^ 256 * d.gW 4 ^ 256 := by
  rw [Fintype.prod_prod_type, Fin.prod_univ_five]
  simp only [prod_const, card_univ, Fintype.card_fin]

theorem sum_gW_fin (j : IA) :
    ∑ k : Fin (d.kap j), d.cf j.1 k * d.X ^ ((k : ℕ) - d.P j.1) = d.gW j.1 := by
  rw [d.gW_eq, Fin.sum_univ_eq_sum_range (fun k => d.cf j.1 k * d.X ^ (k - d.P j.1))]

theorem w_sp (ω : d.OA) : d.w ω * d.X ^ d.sp ω =
    ∏ i : IA, (d.cf i.1 (ω i) * d.X ^ ((ω i : ℕ) - d.P i.1)) := by
  rw [w, sp, prod_mul_distrib, prod_pow_eq_pow_sum]

theorem genW : ∑ ω, d.w ω * d.X ^ d.sp ω = ∏ j : IA, d.gW j.1 := by
  simp_rw [w_sp]
  rw [sum_prod_pi (fun (i : IA) (k : Fin (d.kap i)) => d.cf i.1 k * d.X ^ ((k : ℕ) - d.P i.1))]
  exact prod_congr rfl fun j _ => d.sum_gW_fin j

theorem genPay (i : IA) :
    (∑ ω : d.OA, (d.w ω * d.X ^ d.sp ω) * (if d.P i.1 ≤ (ω i : ℕ) then d.P i.1 else 0)) =
    d.hW i.1 * ∏ j ∈ univ.erase i, d.gW j.1 := by
  simp_rw [w_sp]
  have h := sum_prod_marg d.kap (fun (j : IA) k => d.cf j.1 k * d.X ^ (k - d.P j.1))
    (fun k => if d.P i.1 ≤ k then d.P i.1 else 0) i
  rw [h, d.hW_eq, Fin.sum_univ_eq_sum_range
    (fun k => d.cf i.1 k * d.X ^ (k - d.P i.1) * if d.P i.1 ≤ k then d.P i.1 else 0)]
  congr 1
  exact prod_congr rfl fun j _ => d.sum_gW_fin j

theorem erase_gW (τ : Fin 5) (c : Fin 256) (Q : ℕ)
    (hQ : d.gW τ * Q =
      d.gW 0 ^ 256 * d.gW 1 ^ 256 * d.gW 2 ^ 256 * d.gW 3 ^ 256 * d.gW 4 ^ 256) :
    ∏ j ∈ univ.erase ((τ, c) : IA), d.gW j.1 = Q := by
  refine Nat.eq_of_mul_eq_mul_left (d.gW_pos τ) ?_
  rw [hQ, ← prod_all_gW]
  exact mul_prod_erase univ (fun j : IA => d.gW j.1) (mem_univ (τ, c))

theorem pow_split (a : ℕ) : a ^ 256 = a * a ^ 255 := by rw [← pow_succ']

theorem erase_gW0 (c : Fin 256) : ∏ j ∈ univ.erase ((0, c) : IA), d.gW j.1 =
    d.gW 0 ^ 255 * d.gW 1 ^ 256 * d.gW 2 ^ 256 * d.gW 3 ^ 256 * d.gW 4 ^ 256 := by
  refine d.erase_gW 0 c _ ?_
  rw [pow_split (d.gW 0)]
  generalize d.gW 0 ^ 255 = b, d.gW 1 ^ 256 = a1, d.gW 2 ^ 256 = a2, d.gW 3 ^ 256 = a3,
    d.gW 4 ^ 256 = a4
  ring
theorem erase_gW1 (c : Fin 256) : ∏ j ∈ univ.erase ((1, c) : IA), d.gW j.1 =
    d.gW 0 ^ 256 * d.gW 1 ^ 255 * d.gW 2 ^ 256 * d.gW 3 ^ 256 * d.gW 4 ^ 256 := by
  refine d.erase_gW 1 c _ ?_
  rw [pow_split (d.gW 1)]
  generalize d.gW 0 ^ 256 = a0, d.gW 1 ^ 255 = b, d.gW 2 ^ 256 = a2, d.gW 3 ^ 256 = a3,
    d.gW 4 ^ 256 = a4
  ring
theorem erase_gW2 (c : Fin 256) : ∏ j ∈ univ.erase ((2, c) : IA), d.gW j.1 =
    d.gW 0 ^ 256 * d.gW 1 ^ 256 * d.gW 2 ^ 255 * d.gW 3 ^ 256 * d.gW 4 ^ 256 := by
  refine d.erase_gW 2 c _ ?_
  rw [pow_split (d.gW 2)]
  generalize d.gW 0 ^ 256 = a0, d.gW 1 ^ 256 = a1, d.gW 2 ^ 255 = b, d.gW 3 ^ 256 = a3,
    d.gW 4 ^ 256 = a4
  ring
theorem erase_gW3 (c : Fin 256) : ∏ j ∈ univ.erase ((3, c) : IA), d.gW j.1 =
    d.gW 0 ^ 256 * d.gW 1 ^ 256 * d.gW 2 ^ 256 * d.gW 3 ^ 255 * d.gW 4 ^ 256 := by
  refine d.erase_gW 3 c _ ?_
  rw [pow_split (d.gW 3)]
  generalize d.gW 0 ^ 256 = a0, d.gW 1 ^ 256 = a1, d.gW 2 ^ 256 = a2, d.gW 3 ^ 255 = b,
    d.gW 4 ^ 256 = a4
  ring
theorem erase_gW4 (c : Fin 256) : ∏ j ∈ univ.erase ((4, c) : IA), d.gW j.1 =
    d.gW 0 ^ 256 * d.gW 1 ^ 256 * d.gW 2 ^ 256 * d.gW 3 ^ 256 * d.gW 4 ^ 255 := by
  refine d.erase_gW 4 c _ ?_
  rw [pow_split (d.gW 4)]
  generalize d.gW 0 ^ 256 = a0, d.gW 1 ^ 256 = a1, d.gW 2 ^ 256 = a2, d.gW 3 ^ 256 = a3,
    d.gW 4 ^ 255 = b
  ring

theorem yfull_alg (E a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 h0 h1 h2 h3 h4 : ℕ) :
    E * (a0 * a1 * a2 * a3 * a4) +
    (256 * (h0 * (b0 * a1 * a2 * a3 * a4)) + 256 * (h1 * (a0 * b1 * a2 * a3 * a4)) +
     256 * (h2 * (a0 * a1 * b2 * a3 * a4)) + 256 * (h3 * (a0 * a1 * a2 * b3 * a4)) +
     256 * (h4 * (a0 * a1 * a2 * a3 * b4))) =
    E * (a0 * a1 * a2 * a3 * a4)
  + (256 * h0 * b0) * a1 * a2 * a3 * a4 + a0 * (256 * h1 * b1) * a2 * a3 * a4
  + a0 * a1 * (256 * h2 * b2) * a3 * a4 + a0 * a1 * a2 * (256 * h3 * b3) * a4
  + a0 * a1 * a2 * a3 * (256 * h4 * b4) := by
  ring

theorem genY : ∑ ω, d.w2 ω * d.X ^ d.sp ω = yfull d.e d.gW d.hW := by
  have h1 : ∀ ω : d.OA, d.w2 ω * d.X ^ d.sp ω = d.e * (d.w ω * d.X ^ d.sp ω) +
      ∑ i : IA, (d.w ω * d.X ^ d.sp ω) * (if d.P i.1 ≤ (ω i : ℕ) then d.P i.1 else 0) := by
    intro ω; rw [w2, py, ← mul_sum]; ring
  simp_rw [h1]
  rw [sum_add_distrib, ← mul_sum, genW, sum_comm, prod_all_gW]
  simp_rw [genPay]
  rw [Fintype.sum_prod_type, Fin.sum_univ_five]
  simp only [erase_gW0, erase_gW1, erase_gW2, erase_gW3, erase_gW4, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul]
  rw [yfull]
  exact yfull_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem sum_pay_one (i : IA) :
    (∑ ω : d.OA, d.w ω * (if d.P i.1 ≤ (ω i : ℕ) then d.P i.1 else 0)) * d.W
      = d.pay i.1 * d.Dn := by
  rw [d.marg_w (fun k => if d.P i.1 ≤ k then d.P i.1 else 0) i, ← d.pay_eq]

theorem sum_w2 : (∑ ω, d.w2 ω) * d.W = d.Epay * d.Dn := by
  have h1 : ∀ ω : d.OA, d.w2 ω = d.e * d.w ω +
      ∑ i : IA, d.w ω * (if d.P i.1 ≤ (ω i : ℕ) then d.P i.1 else 0) := by
    intro ω; rw [w2, py, ← mul_sum]; ring
  simp_rw [h1]
  rw [sum_add_distrib, ← mul_sum, sum_w, sum_comm, add_mul, sum_mul]
  simp_rw [sum_pay_one]
  rw [← sum_mul, Fintype.sum_prod_type, Fin.sum_univ_five]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [d.Epay_eq]
  ring

theorem sum_w2_lt : ∑ ω, d.w2 ω < d.X := by
  refine Nat.lt_of_mul_lt_mul_right (a := d.W) ?_
  rw [sum_w2, d.X_eq]
  calc d.Epay * d.Dn < (d.W * d.W) * d.Dn := Nat.mul_lt_mul_of_pos_right d.Epay_lt d.Dn_pos
    _ = d.Dn * d.W * d.W := by ring

theorem dY_sum (j : ℕ) (hj : j < d.e) : d.dY j = ∑ ω, if d.sp ω = j then d.w2 ω else 0 := by
  rw [d.dY_eq j hj, ← genY]
  exact digit_sum d.w2 d.sp d.X d.sum_w2_lt j

theorem Qloss_eq : ∑ j ∈ range d.e, d.dY j = ∑ ω, if d.sp ω < d.e then d.w2 ω else 0 := by
  rw [sum_congr rfl (fun j hj => d.dY_sum j (mem_range.mp hj)), sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [sum_ite_eq (range d.e) (d.sp ω) (fun _ => d.w2 ω)]
  simp

theorem rev_nat : 119464 * (d.N * d.Dn) ≤ 100000 * ∑ ω, if d.e ≤ d.sp ω then d.w2 ω else 0 := by
  have h := d.rev
  rw [← sum_w2] at h
  have h2 : (∑ ω, if d.e ≤ d.sp ω then d.w2 ω else 0) + ∑ j ∈ range d.e, d.dY j
      = ∑ ω, d.w2 ω := by
    rw [Qloss_eq, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ => ?_
    by_cases hh : d.e ≤ d.sp ω
    · rw [if_pos hh, if_neg (by omega), add_zero]
    · rw [if_neg hh, if_pos (by omega), zero_add]
  rw [← h2] at h
  refine le_of_mul_le_mul_left ?_ d.W_pos
  nlinarith [h]

end Data
end Sievert26SimpleAuctions
