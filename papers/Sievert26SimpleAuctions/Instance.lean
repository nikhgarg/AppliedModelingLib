import Sievert26SimpleAuctions.GroupAData
import Sievert26SimpleAuctions.KernelRun

/-! The concrete group `A`: all fields of `Data` are discharged from the kernel certificates. -/
set_option linter.deprecated false
open Finset

namespace Sievert26SimpleAuctions
namespace Cert

theorem Dn_eq : Dn = W ^ 1280 := by
  unfold Dn W
  rw [show (30720 : ℕ) = 24 * 1280 from by norm_num, pow_mul]

theorem X_eq : X = Dn * W := by
  unfold X s Dn W
  rw [show (30744 : ℕ) = 30720 + 24 from by norm_num, pow_add]

theorem EZ_eq : EZ = 256 * (meanA 0 + meanA 1 + meanA 2 + meanA 3 + meanA 4) := by
  unfold EZ; rfl

theorem EpayNum_eq :
    EpayNum = e * W + 256 * (payA 0 + payA 1 + payA 2 + payA 3 + payA 4) := by
  unfold EpayNum; rfl

theorem EpayNum_lt : EpayNum < W * W := by decide +kernel

theorem pay_eq (i : Fin 5) :
    ∑ k ∈ range (P i + e + 1), cf (R i) (P i) k * (if P i ≤ k then P i else 0) = payA i := by
  have h := pay_gen (R i) (P i) 1
  simp only [one_pow, mul_one] at h
  rw [h, ← mul_sum, payA]
  refine congrArg (P i * ·) ?_
  have h2 := sum_cf_add (R i) (P i) (P_pos _) (RP_le _) (P i)
  have h3 := sum_cf (R i) (P i) (P_pos _) (RP_le _)
  rw [show P i + e + 1 = P i + (e+1) by ring, sum_range_add] at h3
  generalize ∑ x ∈ range (e+1), cf (R i) (P i) (P i + x) = a at h3 ⊢
  generalize ∑ x ∈ range (P i), cf (R i) (P i) x = b at h2 h3
  generalize tl (R i) (P i) (P i) = c at h2 ⊢
  generalize W = W' at h2 h3
  omega

theorem FA_digit (t : ℕ) (ht : t < T) : digit FA t = (∏ i : Fin 5, gA i ^ 256) / X ^ t % X := by
  rw [digit, FA_eq, mod_digit _ _ _ _ ht]

theorem YW_digit (j : ℕ) (hj : j < e) : digit YW j = yfull e gW hW / X ^ j % X := by
  rw [digit, YW_eq, mod_digit _ _ _ _ hj]

theorem YW_digit_big (j : ℕ) (hj : e ≤ j) : digit YW j = 0 := by
  have : YW < X ^ j := by
    rw [YW_eq]
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos X_pos)) (Nat.pow_le_pow_right X_pos hj)
  rw [digit, Nat.div_eq_of_lt this, Nat.zero_mod]

theorem Qloss_eq : Qloss = ∑ j ∈ range e, digit YW j := by
  unfold Qloss
  rw [sumTree_eq]
  simp only [zero_add]
  exact sum_range_ext (digit YW) (by simp [e]) YW_digit_big

theorem outer_facts :
    (∀ t, 0 < t → t ≤ T → (N + t) * (Dn - Cs (digit FA) t) ≤ N * Dn) ∧
      finalCheck (Cs (digit FA) T) (Ss (digit FA) T) = true := by
  have hb := brevCheck_true
  rw [brevCheck] at hb
  have c0 : Cs (digit FA) (50 * 0) = 0 := by unfold Cs; rw [mul_zero, sum_range_zero]
  have s0 : Ss (digit FA) (50 * 0) = 0 := by unfold Ss; rw [mul_zero, sum_range_zero]
  have hT : 50 * (0 + 40) = T := by unfold T; norm_num
  have h := outer_spec (digit FA) FA finalCheck 40 0 (fun _ _ => rfl) (by rw [c0, s0]; exact hb)
  rw [hT, mul_zero] at h
  exact h

theorem final_fact : EZ * Dn + W * Ss (digit FA) T ≤ W * ((N + T) * Cs (digit FA) T) := by
  have h := outer_facts.2
  rw [finalCheck] at h
  exact Nat.le_of_ble_eq_true h

theorem rev_fact : 100000 * (W * ∑ j ∈ range e, digit YW j) + 119464 * (N * (W * Dn)) ≤
    100000 * (EpayNum * Dn) := by
  have h := revCheck_true
  rw [revCheck] at h
  rw [← Qloss_eq]
  exact Nat.le_of_ble_eq_true h

/-- The concrete instance. -/
def theData : Data where
  N := N
  e := e
  T := T
  X := X
  W := W
  Dn := Dn
  EZ := EZ
  Epay := EpayNum
  P := P
  cf := fun i => cf (R i) (P i)
  gA := gA
  gW := gW
  hW := hW
  mean := meanA
  pay := payA
  dF := digit FA
  dY := digit YW
  R := R
  N_pos := by simp [N]
  e_pos := by simp [e]
  tail_le := fun i m n => (Nat.mul_le_mul_left m
    (sum_cf_tail_le _ _ (P_pos i) (RP_le i) m n)).trans (mul_tl_le _ _ _)
  R_sum := by decide
  W_gt := by simp [W]
  Dn_eq := Dn_eq
  X_eq := X_eq
  sum_cf := fun i => sum_cf _ _ (P_pos i) (RP_le i)
  gA_eq := gA_eq
  mean_eq := meanA_eq
  gW_eq := gW_eq
  hW_eq := hW_eq
  pay_eq := pay_eq
  EZ_eq := EZ_eq
  Epay_eq := EpayNum_eq
  Epay_lt := EpayNum_lt
  dF_eq := FA_digit
  dY_eq := YW_digit
  check := outer_facts.1
  final := final_fact
  rev := rev_fact

end Cert
end Sievert26SimpleAuctions
