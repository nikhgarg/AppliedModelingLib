import Sievert26SimpleAuctions.Kernel

/-! Specifications of the kernel computations: what the packed integers mean. -/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
open Finset

namespace Sievert26SimpleAuctions
namespace Cert

theorem X_pos : 0 < X := by unfold X; exact Nat.two_pow_pos _

theorem pack_eq (c : ℕ → ℕ) (d lo : ℕ) :
    pack c d lo = ∑ j ∈ range (2 ^ d), c (lo + j) * X ^ j := by
  induction d generalizing lo with
  | zero => simp [pack]
  | succ d ih =>
    rw [pack, ih, ih, pow_succ, mul_two, sum_range_add, sum_mul]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [pow_add, add_assoc]; ring

theorem sumTree_eq (c : ℕ → ℕ) (d lo : ℕ) :
    sumTree c d lo = ∑ j ∈ range (2 ^ d), c (lo + j) := by
  induction d generalizing lo with
  | zero => simp [sumTree]
  | succ d ih =>
    rw [sumTree, ih, ih, pow_succ, mul_two, sum_range_add]
    simp only [add_assoc]

theorem pm1_modEq (M g k : ℕ) : pm1 M g k ≡ g ^ (2 ^ k - 1) [MOD M] := by
  induction k with
  | zero => simp [pm1]; rfl
  | succ k ih =>
    have h : 2 ^ (k+1) - 1 = (2 ^ k - 1) + (2 ^ k - 1) + 1 := by
      have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega
    rw [pm1, h, pow_succ, pow_add]
    exact (Nat.mod_modEq _ _).trans
      (((Nat.mod_modEq _ _).trans (ih.mul ih)).mul_right g)

theorem sum_range_ext (f : ℕ → ℕ) {n m : ℕ} (hnm : n ≤ m) (h : ∀ k, n ≤ k → f k = 0) :
    ∑ k ∈ range m, f k = ∑ k ∈ range n, f k := by
  symm
  refine sum_subset (range_mono hnm) fun k _ hk => h k ?_
  simpa using hk

/-- Reading off a base-`x` digit of `Σ_ω w(ω) x^{z(ω)}`. -/
theorem digit_sum {Ω : Type*} [Fintype Ω] (w z : Ω → ℕ) (x : ℕ) (hx : ∑ ω, w ω < x) (t : ℕ) :
    (∑ ω, w ω * x ^ z ω) / x ^ t % x = ∑ ω, if z ω = t then w ω else 0 := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.zero_le _) hx
  set a := ∑ ω, if z ω = t then w ω else 0 with ha
  set L := ∑ ω, if z ω < t then w ω * x ^ z ω else 0 with hL
  set r := ∑ ω, if t < z ω then w ω * x ^ (z ω - t - 1) else 0 with hr
  have hF : ∑ ω, w ω * x ^ z ω = L + x ^ t * (a + x * r) := by
    rw [ha, hL, hr, mul_add, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ => ?_
    rcases lt_trichotomy (z ω) t with h | h | h
    · simp [h, h.ne, h.le, not_lt.mpr h.le]
    · simp [h, mul_comm]
    · have h1 : z ω = t + 1 + (z ω - t - 1) := by omega
      have h2 : ¬ z ω < t := by omega
      have h3 : z ω ≠ t := by omega
      simp only [h, h2, h3, ite_true, ite_false, mul_zero, zero_add]
      conv_lhs => rw [h1, pow_add, pow_succ]
      ring
  have hLlt : L < x ^ t := by
    rcases t with _ | u
    · simp [hL]
    · have : L ≤ ∑ ω, w ω * x ^ u := by
        refine sum_le_sum fun ω _ => ?_
        split_ifs with h
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx0 (by omega))
        · exact Nat.zero_le _
      rw [← sum_mul] at this
      calc L ≤ (∑ ω, w ω) * x ^ u := this
        _ < x * x ^ u := Nat.mul_lt_mul_of_pos_right hx (Nat.pow_pos hx0)
        _ = x ^ (u+1) := by rw [pow_succ, mul_comm]
  have hax : a < x := by
    refine lt_of_le_of_lt (sum_le_sum fun ω _ => ?_) hx
    split_ifs <;> simp
  rw [hF, Nat.add_mul_div_left _ _ (Nat.pow_pos hx0), Nat.div_eq_of_lt hLlt, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hax]

/-- Reducing modulo `x^n` does not change digits below `n`. -/
theorem mod_digit (F x n t : ℕ) (ht : t < n) : F % x ^ n / x ^ t % x = F / x ^ t % x := by
  have h : x ^ n = x ^ t * x ^ (n - t) := by rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self x (by omega : n - t ≠ 0))]

/-- prefix sums and their prefix sums -/
def Cs (a : ℕ → ℕ) (t : ℕ) : ℕ := ∑ i ∈ range t, a i
def Ss (a : ℕ → ℕ) (t : ℕ) : ℕ := ∑ i ∈ range t, Cs a (i+1)

theorem Cs_succ (a : ℕ → ℕ) (t : ℕ) : Cs a (t+1) = Cs a t + a t := sum_range_succ _ _
theorem Ss_succ (a : ℕ → ℕ) (t : ℕ) : Ss a (t+1) = Ss a t + Cs a (t+1) := sum_range_succ _ _

theorem inner_spec (a : ℕ → ℕ) (F t0 : ℕ) (k : ℕ → ℕ → Bool) (f : ℕ) : ∀ j : ℕ,
    (∀ l < f, digit F (j + l) = a (t0 + j + l)) →
    inner F t0 k f j (Cs a (t0 + j)) (Ss a (t0 + j)) = true →
    (∀ l < f, (N + (t0 + j + l + 1)) * (Dn - Cs a (t0 + j + l + 1)) ≤ N * Dn) ∧
      k (Cs a (t0 + j + f)) (Ss a (t0 + j + f)) = true := by
  induction f with
  | zero => intro j _ h; exact ⟨by simp, by simpa [inner] using h⟩
  | succ f ih =>
    intro j hd h
    have hd0 : digit F j = a (t0 + j) := by simpa using hd 0 (by omega)
    rw [inner, hd0, ← Cs_succ, ← Ss_succ, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, _, h3⟩ := h
    have h1' := Nat.le_of_ble_eq_true h1
    have := ih (j+1) (fun l hl => by
      have := hd (l+1) (by omega)
      rw [show j + 1 + l = j + (l+1) by ring, show t0 + (j+1) + l = t0 + j + (l+1) by ring]
      exact this) (by rw [show t0 + (j+1) = t0 + j + 1 by ring]; exact h3)
    refine ⟨fun l hl => ?_, ?_⟩
    · rcases l with _ | l
      · simpa using h1'
      · have := this.1 l (by omega)
        rw [show t0 + (j+1) + l + 1 = t0 + j + (l+1) + 1 by ring] at this
        exact this
    · rw [show t0 + j + (f+1) = t0 + (j+1) + f by ring]; exact this.2

theorem digit_block (F b l : ℕ) (hl : l < 50) :
    digit (F / X ^ (50 * b) % X ^ 50) l = digit F (50 * b + l) := by
  unfold digit
  rw [mod_digit _ _ _ _ hl, Nat.div_div_eq_div_mul, pow_add]

theorem outer_spec (a : ℕ → ℕ) (F : ℕ) (fin : ℕ → ℕ → Bool) (f : ℕ) : ∀ b : ℕ,
    (∀ t < 50 * (b + f), digit F t = a t) →
    outer F fin f b (Cs a (50 * b)) (Ss a (50 * b)) = true →
    (∀ t, 50 * b < t → t ≤ 50 * (b + f) → (N + t) * (Dn - Cs a t) ≤ N * Dn) ∧
      fin (Cs a (50 * (b + f))) (Ss a (50 * (b + f))) = true := by
  induction f with
  | zero => intro b _ h; exact ⟨fun t h1 h2 => by omega, by simpa [outer] using h⟩
  | succ f ih =>
    intro b hd h
    rw [outer] at h
    have h2 := inner_spec a _ (50 * b) _ 50 0 (fun l hl => by
      rw [zero_add, digit_block _ _ _ hl, add_zero]; exact hd _ (by omega)) (by simpa using h)
    obtain ⟨h3, h4⟩ := h2
    rw [add_zero, show 50 * b + 50 = 50 * (b+1) by ring] at h4
    have h5 := ih (b+1) (fun t ht => hd t (by omega)) h4
    refine ⟨fun t ht1 ht2 => ?_, ?_⟩
    · by_cases htb : t ≤ 50 * (b+1)
      · have := h3 (t - 50 * b - 1) (by omega)
        rw [show 50 * b + 0 + (t - 50 * b - 1) + 1 = t by omega] at this
        exact this
      · exact h5.1 t (by omega) (by omega)
    · rw [show b + (f+1) = b + 1 + f by ring]; exact h5.2

/-! ### Tail counts -/

theorem tl_zero (r p : ℕ) : tl r p 0 = W := rfl

theorem tl_succ (r p k : ℕ) :
    tl r p (k+1) = if k + 1 ≤ p + e then r / max (k+1) p else 0 := by
  change cond (Nat.ble (k+1) (p + e)) (r / cond (Nat.ble (k+1) p) p (k+1)) 0 = _
  by_cases h : k + 1 ≤ p + e
  · rw [if_pos h, Nat.ble_eq_true_of_le h, cond_true]
    by_cases h2 : k + 1 ≤ p
    · rw [Nat.ble_eq_true_of_le h2, cond_true, max_eq_right h2]
    · have : Nat.ble (k+1) p = false := by
        rw [Bool.eq_false_iff]; exact fun hh => h2 (Nat.le_of_ble_eq_true hh)
      rw [this, cond_false, max_eq_left (by omega)]
  · have : Nat.ble (k+1) (p+e) = false := by
      rw [Bool.eq_false_iff]; exact fun hh => h (Nat.le_of_ble_eq_true hh)
    rw [if_neg h, this, cond_false]

theorem tl_big (r p k : ℕ) (hk : p + e < k) : tl r p k = 0 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [tl_succ, if_neg (by omega)]

theorem tl_anti (r p k : ℕ) (hp : 0 < p) (hr : r / p ≤ W) : tl r p (k+1) ≤ tl r p k := by
  rcases k with _ | k
  · rw [tl_zero, tl_succ]
    split_ifs
    · exact (Nat.div_le_div_left (le_max_right _ _) hp).trans hr
    · exact Nat.zero_le _
  · rw [tl_succ, tl_succ]
    split_ifs with h1 h2
    · exact Nat.div_le_div_left (max_le_max_right _ (by omega)) (by omega)
    · omega
    · exact Nat.zero_le _
    · exact le_refl _

theorem mul_tl_le (r p m : ℕ) : m * tl r p m ≤ r := by
  rcases m with _ | m
  · simp
  · rw [tl_succ]
    split_ifs
    · exact (Nat.mul_le_mul_right _ (le_max_left _ _)).trans (Nat.mul_div_le _ _)
    · simp

theorem cf_big (r p k : ℕ) (hk : p + e < k) : cf r p k = 0 := by
  unfold cf; rw [tl_big r p k hk]; simp

section
variable (r p : ℕ) (hp : 0 < p) (hr : r / p ≤ W)
include hp hr

theorem cf_add (k : ℕ) : cf r p k + tl r p (k+1) = tl r p k :=
  Nat.sub_add_cancel (tl_anti r p k hp hr)

theorem sum_cf_add (n : ℕ) : ∑ k ∈ range n, cf r p k + tl r p n = W := by
  induction n with
  | zero => simp [tl_zero]
  | succ n ih => rw [sum_range_succ, add_assoc, cf_add r p hp hr, ih]

theorem sum_cf : ∑ k ∈ range (p + e + 1), cf r p k = W := by
  have := sum_cf_add r p hp hr (p + e + 1)
  rwa [tl_big r p _ (by omega), add_zero] at this

theorem sum_cf_tail_le (m n : ℕ) :
    ∑ k ∈ range n, (if m ≤ k then cf r p k else 0) ≤ tl r p m := by
  suffices h : ∑ k ∈ range n, (if m ≤ k then cf r p k else 0)
      + (if m ≤ n then tl r p n else tl r p m) = tl r p m by omega
  induction n with
  | zero =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · rw [if_neg (by omega)]; simp
  | succ n ih =>
    rw [sum_range_succ]
    have := cf_add r p hp hr n
    rcases lt_trichotomy m (n+1) with h | h | h
    · rw [if_pos (by omega)] at ih ⊢
      rw [if_pos (by omega)]; omega
    · rw [if_neg (by omega)] at ih ⊢
      rw [if_pos (by omega), ← h]; omega
    · rw [if_neg (by omega)] at ih ⊢
      rw [if_neg (by omega)]; omega

theorem sum_mul_cf_aux (n : ℕ) :
    ∑ k ∈ range (n+1), cf r p k * k + n * tl r p (n+1) = ∑ k ∈ range n, tl r p (k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ (fun k => tl r p (k+1))]
    have := cf_add r p hp hr (n+1)
    rw [← ih, ← this]; ring

theorem sum_mul_cf : ∑ k ∈ range (p + e + 1), cf r p k * k = ∑ k ∈ range (p+e), tl r p (k+1) := by
  have := sum_mul_cf_aux r p hp hr (p+e)
  rwa [tl_big r p _ (by omega), mul_zero, add_zero] at this

/-- packed surplus generating function -/
theorem surplus_gen (x : ℕ) : ∑ k ∈ range (p + e + 1), cf r p k * x ^ (k - p) =
    ∑ j ∈ range (e+1), gcoef r p j * x ^ j := by
  rw [show p + e + 1 = (p + 1) + e by ring, sum_range_add, sum_range_succ' _ e, add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun j _ => ?_
    rw [show p + 1 + j - p = j + 1 by omega, show p + 1 + j = p + (j+1) by ring]
    rfl
  · have h := sum_cf_add r p hp hr (p+1)
    rw [pow_zero, mul_one]
    change _ = W - tl r p (p+1)
    rw [← h, Nat.add_sub_cancel]
    refine sum_congr rfl fun k hk => ?_
    rw [Nat.sub_eq_zero_of_le (by have := mem_range.mp hk; omega), pow_zero, mul_one]

end

theorem pay_gen (r p x : ℕ) :
    ∑ k ∈ range (p + e + 1), cf r p k * x ^ (k - p) * (if p ≤ k then p else 0) =
    ∑ j ∈ range (e+1), p * cf r p (p + j) * x ^ j := by
  rw [show p + e + 1 = p + (e + 1) by ring, sum_range_add, sum_eq_zero, zero_add]
  · refine sum_congr rfl fun j _ => ?_
    rw [if_pos (by omega), Nat.add_sub_cancel_left]; ring
  · intro k hk
    rw [if_neg (by have := mem_range.mp hk; omega), mul_zero]

theorem P_pos (i : Fin 5) : 0 < P i := by fin_cases i <;> simp [P]
theorem RP_le (i : Fin 5) : R i / P i ≤ W := by fin_cases i <;> simp [P, R, W]

theorem gA_eq (i : Fin 5) :
    gA i = ∑ k ∈ range (P i + e + 1), cf (R i) (P i) k * X ^ k := by
  unfold gA
  rw [pack_eq]
  simp only [zero_add]
  refine sum_range_ext _ (by fin_cases i <;> simp [P, e]) fun k hk => ?_
  rw [cf_big _ _ _ (by omega), zero_mul]

theorem meanA_eq (i : Fin 5) :
    meanA i = ∑ k ∈ range (P i + e + 1), cf (R i) (P i) k * k := by
  unfold meanA
  rw [sumTree_eq, sum_mul_cf _ _ (P_pos i) (RP_le i)]
  simp only [zero_add]
  refine sum_range_ext _ (by fin_cases i <;> simp [P, e]) fun k hk => ?_
  rw [tl_big _ _ _ (by omega)]

theorem gW_eq (i : Fin 5) :
    gW i = ∑ k ∈ range (P i + e + 1), cf (R i) (P i) k * X ^ (k - P i) := by
  unfold gW
  rw [pack_eq, surplus_gen _ _ (P_pos i) (RP_le i)]
  simp only [zero_add]
  refine sum_range_ext _ (by simp [e]) fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  change cf (R i) (P i) (P i + (j+1)) * _ = 0
  rw [cf_big _ _ _ (by omega), zero_mul]

theorem hW_eq (i : Fin 5) : hW i = ∑ k ∈ range (P i + e + 1),
    cf (R i) (P i) k * X ^ (k - P i) * (if P i ≤ k then P i else 0) := by
  unfold hW
  rw [pack_eq, pay_gen]
  simp only [zero_add]
  refine sum_range_ext _ (by simp [e]) fun k hk => ?_
  rw [cf_big _ _ _ (by omega), mul_zero, zero_mul]

theorem pA_modEq (i : Fin 5) : pA i ≡ gA i ^ 256 [MOD MT] := by
  unfold pA
  exact (Nat.mod_modEq _ _).trans ((pm1_modEq MT (gA i) 8).mul_right (gA i))

theorem mul_mod_step {M a b c d : ℕ} (h1 : a ≡ b [MOD M]) (h2 : c ≡ d [MOD M]) :
    a * c % M ≡ b * d [MOD M] := (Nat.mod_modEq _ _).trans (h1.mul h2)

theorem mod_of_modEq {M a b : ℕ} (h : a ≡ b [MOD M]) : a % M = b % M := h

theorem prod5_mod {M a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ} (h0 : a0 ≡ b0 [MOD M])
    (h1 : a1 ≡ b1 [MOD M]) (h2 : a2 ≡ b2 [MOD M]) (h3 : a3 ≡ b3 [MOD M]) (h4 : a4 ≡ b4 [MOD M]) :
    (((a0 * a1 % M) * a2 % M) * a3 % M) * a4 ≡ b0 * b1 * b2 * b3 * b4 [MOD M] :=
  (mul_mod_step (mul_mod_step (mul_mod_step h0 h1) h2) h3).mul h4

theorem FA_eq_gen (F M XT : ℕ) (a g : Fin 5 → ℕ)
    (hF : F = (((a 0 * a 1 % M) * a 2 % M) * a 3 % M) * a 4 % M)
    (ha : ∀ i, a i ≡ g i ^ 256 [MOD M]) (hM : M = XT) : F = (∏ i : Fin 5, g i ^ 256) % XT := by
  subst hM
  rw [hF, Fin.prod_univ_five]
  exact mod_of_modEq (prod5_mod (ha 0) (ha 1) (ha 2) (ha 3) (ha 4))

theorem FA_def : FA = (((pA 0 * pA 1 % MT) * pA 2 % MT) * pA 3 % MT) * pA 4 % MT := by rw [FA]

theorem FA_eq : FA = (∏ i : Fin 5, gA i ^ 256) % X ^ T := by
  have hM : MT = X ^ T := by unfold MT; rfl
  exact FA_eq_gen FA MT (X ^ T) pA gA FA_def pA_modEq hM

theorem q255_modEq (i : Fin 5) : q255 i ≡ gW i ^ 255 [MOD Me] := by
  unfold q255; exact pm1_modEq Me (gW i) 8
theorem q256_modEq (i : Fin 5) : q256 i ≡ gW i ^ 256 [MOD Me] := by
  unfold q256
  exact (Nat.mod_modEq _ _).trans ((q255_modEq i).mul_right (gW i))
theorem hq_modEq (i : Fin 5) : hq i ≡ 256 * hW i * gW i ^ 255 [MOD Me] := by
  unfold hq
  exact (Nat.mod_modEq _ _).trans ((q255_modEq i).mul_left _)

/-- The un-reduced generating function of `(entry fee + item payments)` by surplus. -/
def yfull (E : ℕ) (g h : Fin 5 → ℕ) : ℕ :=
  E * (g 0 ^ 256 * g 1 ^ 256 * g 2 ^ 256 * g 3 ^ 256 * g 4 ^ 256)
  + (256 * h 0 * g 0 ^ 255) * g 1 ^ 256 * g 2 ^ 256 * g 3 ^ 256 * g 4 ^ 256
  + g 0 ^ 256 * (256 * h 1 * g 1 ^ 255) * g 2 ^ 256 * g 3 ^ 256 * g 4 ^ 256
  + g 0 ^ 256 * g 1 ^ 256 * (256 * h 2 * g 2 ^ 255) * g 3 ^ 256 * g 4 ^ 256
  + g 0 ^ 256 * g 1 ^ 256 * g 2 ^ 256 * (256 * h 3 * g 3 ^ 255) * g 4 ^ 256
  + g 0 ^ 256 * g 1 ^ 256 * g 2 ^ 256 * g 3 ^ 256 * (256 * h 4 * g 4 ^ 255)

theorem YW_generic {M a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 E : ℕ}
    (h0 : a0 ≡ b0 [MOD M])
    (h1 : a1 ≡ b1 [MOD M]) (h2 : a2 ≡ b2 [MOD M]) (h3 : a3 ≡ b3 [MOD M]) (h4 : a4 ≡ b4 [MOD M])
    (k0 : c0 ≡ d0 [MOD M])
    (k1 : c1 ≡ d1 [MOD M]) (k2 : c2 ≡ d2 [MOD M]) (k3 : c3 ≡ d3 [MOD M]) (k4 : c4 ≡ d4 [MOD M]) :
    (E * (a0 * a1 % M * a2 % M * a3 % M * a4 % M)
    + c0 * a1 % M * a2 % M * a3 % M * a4 + a0 * c1 % M * a2 % M * a3 % M * a4
    + a0 * a1 % M * c2 % M * a3 % M * a4 + a0 * a1 % M * a2 % M * c3 % M * a4
    + a0 * a1 % M * a2 % M * a3 % M * c4) % M =
    (E * (b0 * b1 * b2 * b3 * b4) + d0 * b1 * b2 * b3 * b4 + b0 * d1 * b2 * b3 * b4
    + b0 * b1 * d2 * b3 * b4 + b0 * b1 * b2 * d3 * b4 + b0 * b1 * b2 * b3 * d4) % M :=
  mod_of_modEq ((((((((Nat.mod_modEq _ _).trans (prod5_mod h0 h1 h2 h3 h4)).mul_left E).add
    (prod5_mod k0 h1 h2 h3 h4)).add (prod5_mod h0 k1 h2 h3 h4)).add
    (prod5_mod h0 h1 k2 h3 h4)).add (prod5_mod h0 h1 h2 k3 h4)).add (prod5_mod h0 h1 h2 h3 k4))

def ymod (M E : ℕ) (q k : Fin 5 → ℕ) : ℕ :=
  (E * (q 0 * q 1 % M * q 2 % M * q 3 % M * q 4 % M)
  + k 0 * q 1 % M * q 2 % M * q 3 % M * q 4
  + q 0 * k 1 % M * q 2 % M * q 3 % M * q 4
  + q 0 * q 1 % M * k 2 % M * q 3 % M * q 4
  + q 0 * q 1 % M * q 2 % M * k 3 % M * q 4
  + q 0 * q 1 % M * q 2 % M * q 3 % M * k 4) % M

theorem YW_eq_gen (Y M E XT : ℕ) (q k g h : Fin 5 → ℕ) (hY : Y = ymod M E q k)
    (hq : ∀ i, q i ≡ g i ^ 256 [MOD M]) (hk : ∀ i, k i ≡ 256 * h i * g i ^ 255 [MOD M])
    (hM : M = XT) : Y = yfull E g h % XT := by
  subst hM
  rw [hY, ymod, yfull]
  exact YW_generic (hq 0) (hq 1) (hq 2) (hq 3) (hq 4) (hk 0) (hk 1) (hk 2) (hk 3) (hk 4)

theorem YW_def : YW = ymod Me e q256 hq := by rw [YW, ymod]

theorem YW_eq : YW = yfull e gW hW % X ^ e := by
  have hM : Me = X ^ e := by unfold Me; rfl
  exact YW_eq_gen YW Me e (X ^ e) q256 hq gW hW YW_def q256_modEq hq_modEq hM

end Cert
end Sievert26SimpleAuctions
