import Sievert26SimpleAuctions.AnalyticCert
import Sievert26SimpleAuctions.CertKernel

/-! Soundness of the integer checker: what its answers mean for real numbers. -/
set_option linter.deprecated false
open Finset MeasureTheory

namespace Sievert26SimpleAuctions
namespace UB
open UBCert

/-! ### casts -/

theorem SC_pos : (0:ℝ) < (SC : ℕ) := by unfold SC; norm_num
theorem Dd_pos : (0:ℝ) < (Dd : ℕ) := by unfold Dd; norm_num
theorem Dx_pos : (0:ℝ) < (Dx : ℕ) := by unfold Dx; norm_num
theorem UN_pos : (0:ℝ) < (UN : ℕ) := by unfold UN; norm_num

theorem cdiv_le (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℕ) := by
  have h : a ≤ b * cdiv a b := by
    unfold cdiv
    have h1 := Nat.div_add_mod (a + b - 1) b
    have h2 := Nat.mod_lt (a + b - 1) hb
    generalize b * ((a + b - 1) / b) = q at *
    omega
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have : (a:ℝ) ≤ ((b * cdiv a b : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_mul] at this
  linarith

theorem natsub_le (a b : ℕ) : ((a - b : ℕ) : ℝ) ≤ max ((a:ℝ) - b) 0 := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]; exact le_max_left _ _
  · rw [Nat.sub_eq_zero_of_le h]; simp

theorem le_natsub (a b : ℕ) : (a:ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a:ℝ) ≤ b := by exact_mod_cast h
    simp; linarith

/-! ### exponentials -/

theorem polyLo_le (X : ℕ) : (polyLo X : ℝ) ≤ SC * Real.exp (-((X:ℝ) / SC)) := by
  have hS := SC_pos
  unfold polyLo
  refine (natsub_le _ _).trans (max_le ?_ (by positivity))
  have h1 : ((X * X / (2 * SC) : ℕ) : ℝ) ≤ (X:ℝ) * X / (2 * SC) := by
    refine Nat.cast_div_le.trans (le_of_eq ?_); push_cast; ring
  have h2 : (X:ℝ) * X * X / (6 * SC * SC) ≤ (cdiv (X * X * X) (6 * SC * SC) : ℕ) := by
    have := cdiv_le (X * X * X) (6 * SC * SC) (by unfold SC; norm_num)
    refine le_trans (le_of_eq ?_) this
    push_cast; ring
  have h3 := cubic_le_exp_neg ((X:ℝ) / SC) (by positivity)
  have h4 := mul_le_mul_of_nonneg_left h3 hS.le
  refine le_trans ?_ h4
  push_cast
  have e : (SC:ℝ) * (1 - (X:ℝ) / SC + ((X:ℝ) / SC) ^ 2 / 2 - ((X:ℝ) / SC) ^ 3 / 6) =
      SC + (X:ℝ) * X / (2 * SC) - (X + (X:ℝ) * X * X / (6 * SC * SC)) := by
    field_simp; ring
  rw [e]
  push_cast at h1 h2
  linarith

theorem le_polyUp (X : ℕ) : SC * Real.exp (-((X:ℝ) / SC)) ≤ (polyUp X : ℝ) := by
  have hS := SC_pos
  unfold polyUp
  refine le_trans ?_ (le_natsub _ _)
  have h2 : (X:ℝ) * X / (2 * SC) ≤ (cdiv (X * X) (2 * SC) : ℕ) := by
    have := cdiv_le (X * X) (2 * SC) (by unfold SC; norm_num)
    refine le_trans (le_of_eq ?_) this
    push_cast; ring
  have h3 := exp_neg_le_quad ((X:ℝ) / SC) (by positivity)
  have h4 := mul_le_mul_of_nonneg_left h3 hS.le
  refine h4.trans ?_
  push_cast
  have e : (SC:ℝ) * (1 - (X:ℝ) / SC + ((X:ℝ) / SC) ^ 2 / 2) = SC + (X:ℝ) * X / (2 * SC) - X := by
    field_simp; ring
  rw [e]
  push_cast at h2
  linarith

theorem sqLo_le (k : ℕ) : ∀ (y : ℕ) (t : ℝ), (y : ℝ) ≤ SC * Real.exp (-t) →
    (sqLo SC k y : ℝ) ≤ SC * Real.exp (-(2 ^ k * t)) := by
  induction k with
  | zero => intro y t h; simpa [sqLo] using h
  | succ k ih =>
    intro y t h
    rw [sqLo]
    have hS := SC_pos
    have h1 : ((y * y / SC : ℕ) : ℝ) ≤ SC * Real.exp (-(2 * t)) := by
      refine Nat.cast_div_le.trans ?_
      rw [div_le_iff₀ hS]
      push_cast
      have h2 : (y:ℝ) * y ≤ (SC * Real.exp (-t)) * (SC * Real.exp (-t)) :=
        mul_le_mul h h (Nat.cast_nonneg _) (by positivity)
      have h3 : Real.exp (-(2 * t)) = Real.exp (-t) * Real.exp (-t) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h3]; linarith
    have h2 := ih _ _ h1
    rwa [show (2:ℝ) ^ k * (2 * t) = 2 ^ (k+1) * t by rw [pow_succ]; ring] at h2

theorem le_sqUp (k : ℕ) : ∀ (y : ℕ) (t : ℝ), SC * Real.exp (-t) ≤ (y : ℝ) →
    SC * Real.exp (-(2 ^ k * t)) ≤ (sqUp SC k y : ℝ) := by
  induction k with
  | zero => intro y t h; simpa [sqUp] using h
  | succ k ih =>
    intro y t h
    rw [sqUp]
    have hS := SC_pos
    have h1 : SC * Real.exp (-(2 * t)) ≤ (cdiv (y * y) SC : ℕ) := by
      refine le_trans ?_ (cdiv_le (y * y) SC (by unfold SC; norm_num))
      rw [le_div_iff₀ hS]
      push_cast
      have h2 : (SC * Real.exp (-t)) * (SC * Real.exp (-t)) ≤ (y:ℝ) * y :=
        mul_le_mul h h (by positivity) (Nat.cast_nonneg _)
      have h3 : Real.exp (-(2 * t)) = Real.exp (-t) * Real.exp (-t) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h3]; linarith
    have h2 := ih _ _ h1
    rwa [show (2:ℝ) ^ k * (2 * t) = 2 ^ (k+1) * t by rw [pow_succ]; ring] at h2

theorem expLo_le (a b : ℕ) (hb : 0 < b) :
    (expLo a b : ℝ) ≤ SC * Real.exp (-((a:ℝ) / b)) := by
  have hS := SC_pos
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  unfold expLo
  set k := ek a b
  have hk : 0 < b * 2 ^ k := Nat.mul_pos hb (Nat.two_pow_pos k)
  set X := cdiv (a * SC) (b * 2 ^ k) with hX
  have h0 := cdiv_le (a * SC) (b * 2 ^ k) hk
  have h1 : (a:ℝ) / (b * 2 ^ k) ≤ (X:ℝ) / SC := by
    rw [le_div_iff₀ hS]
    refine le_trans (le_of_eq ?_) h0
    push_cast; ring
  have h2 : (polyLo X : ℝ) ≤ SC * Real.exp (-((a:ℝ) / (b * 2 ^ k))) := by
    refine (polyLo_le X).trans (mul_le_mul_of_nonneg_left ?_ hS.le)
    rw [Real.exp_le_exp]; linarith
  have h3 := sqLo_le k _ _ h2
  refine h3.trans (le_of_eq ?_)
  congr 3
  field_simp

theorem le_expUp (a b : ℕ) (hb : 0 < b) :
    SC * Real.exp (-((a:ℝ) / b)) ≤ (expUp a b : ℝ) := by
  have hS := SC_pos
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  unfold expUp
  set k := ek a b
  set X := a * SC / (b * 2 ^ k) with hX
  have h1 : (X:ℝ) / SC ≤ (a:ℝ) / (b * 2 ^ k) := by
    rw [div_le_iff₀ hS]
    refine (Nat.cast_div_le (m := a * SC) (n := b * 2 ^ k) (α := ℝ)).trans (le_of_eq ?_)
    push_cast; ring
  have h2 : SC * Real.exp (-((a:ℝ) / (b * 2 ^ k))) ≤ (polyUp X : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hS.le) (le_polyUp X)
    rw [Real.exp_le_exp]; linarith
  have h3 := le_sqUp k _ _ h2
  refine le_trans (le_of_eq ?_) h3
  congr 3
  field_simp

theorem psiUp_ge (al v : ℕ) (hal : 0 < al) (hv : 0 < v) :
    SC * psi ((al:ℝ) / v) ≤ (psiUp al v : ℝ) := by
  have hS := SC_pos
  have hal' : (0:ℝ) < al := by exact_mod_cast hal
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  unfold psiUp
  refine le_trans ?_ (le_natsub _ _)
  have h1 := le_expUp al v hv
  have h2 : (v:ℝ) * (SC * Real.exp (-((al:ℝ) / v))) / al ≤ (cdiv (v * expUp al v) al : ℕ) := by
    refine le_trans ?_ (cdiv_le _ _ hal)
    push_cast
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hv'.le) hal'.le
  have h3 : ((SC * v / al : ℕ) : ℝ) ≤ (SC:ℝ) * v / al := by
    refine Nat.cast_div_le.trans (le_of_eq ?_); push_cast; ring
  rw [psi_eq _ _ hal' hv']
  push_cast
  push_cast at h3
  have e : (SC:ℝ) * (1 - (v:ℝ) / al + v / al * Real.exp (-((al:ℝ) / v))) =
      SC - SC * v / al + v * (SC * Real.exp (-((al:ℝ) / v))) / al := by ring
  rw [e]; linarith

/-! ### the kernel `w` -/

noncomputable def aR (i : Fin 4) : ℝ := (AN i : ℝ) / 1000
noncomputable def sR (i : Fin 4) : ℝ := (SN i : ℝ) / 10

theorem SN_pos (i : Fin 4) : 0 < SN i := by fin_cases i <;> simp [SN]
theorem aR_nonneg (i : Fin 4) : 0 ≤ aR i := by unfold aR; positivity
theorem sR_pos (i : Fin 4) : 0 < sR i := by
  have : (0:ℝ) < SN i := by exact_mod_cast SN_pos i
  unfold sR; positivity

/-- one exponential: linear minorant on a cell -/
theorem term_minorant (A S a b : ℕ) (hS : 0 < S) (hab : a < b) (v : ℝ)
    (hva : (a:ℝ) / Dd ≤ v) (hvb : v ≤ (b:ℝ) / Dd) :
    (((b:ℝ) / Dd - v) * wtA A S a b + (v - (a:ℝ) / Dd) * wtB A S a b) / ((b:ℝ) / Dd - (a:ℝ) / Dd) ≤
      SC * ((A:ℝ) / 1000 * Real.exp (-(v / ((S:ℝ) / 10)))) := by
  have hSC := SC_pos
  have hD := Dd_pos
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  have hw : (0:ℝ) < (b:ℝ) / Dd - (a:ℝ) / Dd := by
    rw [← sub_div]; exact div_pos (by linarith) hD
  by_cases hc : (b - a) * 10 ≤ 2 * Dd * S
  · -- active case
    set N : ℕ := 2 * Dd * S with hN
    have hN0 : 0 < N := by rw [hN]; unfold Dd; positivity
    have hN' : (0:ℝ) < N := by exact_mod_cast hN0
    have hcast : (((b - a) * 10 : ℕ) : ℝ) = ((b:ℝ) - a) * 10 := by
      rw [Nat.cast_mul, Nat.cast_sub hab.le]; push_cast; ring
    have hcr : ((b:ℝ) - a) * 10 ≤ N := by rw [← hcast]; exact_mod_cast hc
    set E := Real.exp (-((((a + b) * 10 : ℕ) : ℝ) / N)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hEl := expLo_le ((a + b) * 10) N hN0
    have hA : (wtA A S a b : ℝ) ≤ SC * ((A:ℝ) / 1000 * E * ((N + ((b:ℝ) - a) * 10) / N)) := by
      unfold wtA
      rw [← hN, Nat.ble_eq_true_of_le hc, cond_true]
      refine Nat.cast_div_le.trans ?_
      rw [div_le_iff₀ (by exact_mod_cast Nat.mul_pos (by norm_num) hN0)]
      push_cast [hcast]
      have h1 : (A:ℝ) * (expLo ((a + b) * 10) N) * (N + ((b:ℝ) - a) * 10) ≤
          A * (SC * E) * (N + ((b:ℝ) - a) * 10) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEl (Nat.cast_nonneg _)) ?_
        nlinarith
      refine h1.trans (le_of_eq ?_)
      field_simp
    have hB : (wtB A S a b : ℝ) ≤ SC * ((A:ℝ) / 1000 * E * ((N - ((b:ℝ) - a) * 10) / N)) := by
      unfold wtB
      rw [← hN, Nat.ble_eq_true_of_le hc, cond_true]
      refine Nat.cast_div_le.trans ?_
      rw [div_le_iff₀ (by exact_mod_cast Nat.mul_pos (by norm_num) hN0)]
      push_cast
      rw [Nat.cast_sub hc, hcast]
      have h1 : (A:ℝ) * (expLo ((a + b) * 10) N) * (N - ((b:ℝ) - a) * 10) ≤
          A * (SC * E) * (N - ((b:ℝ) - a) * 10) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEl (Nat.cast_nonneg _)) ?_
        linarith
      refine h1.trans (le_of_eq ?_)
      field_simp
    -- tangent
    have hNr : (N:ℝ) = 2 * Dd * S := by rw [hN]; push_cast; ring
    have htan : E * (1 - (v - ((a:ℝ) + b) / (2 * Dd)) / ((S:ℝ) / 10)) ≤
        Real.exp (-(v / ((S:ℝ) / 10))) := by
      have h1 := Real.add_one_le_exp (-((v - ((a:ℝ) + b) / (2 * Dd)) / ((S:ℝ) / 10)))
      have e : Real.exp (-(v / ((S:ℝ) / 10))) =
          E * Real.exp (-((v - ((a:ℝ) + b) / (2 * Dd)) / ((S:ℝ) / 10))) := by
        rw [hE, ← Real.exp_add]
        congr 1
        rw [hNr]; push_cast; field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hE0.le
    have hlin : (((b:ℝ) / Dd - v) * ((N + ((b:ℝ) - a) * 10) / N) +
        (v - (a:ℝ) / Dd) * ((N - ((b:ℝ) - a) * 10) / N)) / ((b:ℝ) / Dd - (a:ℝ) / Dd) =
        1 - (v - ((a:ℝ) + b) / (2 * Dd)) / ((S:ℝ) / 10) := by
      have hne : (b:ℝ) - a ≠ 0 := by linarith
      rw [hNr, ← sub_div]
      field_simp
      ring
    have hy : 0 ≤ (b:ℝ) / Dd - v := by linarith
    have hx : 0 ≤ v - (a:ℝ) / Dd := by linarith
    calc _ ≤ (((b:ℝ) / Dd - v) * (SC * ((A:ℝ) / 1000 * E * ((N + ((b:ℝ) - a) * 10) / N))) +
          (v - (a:ℝ) / Dd) * (SC * ((A:ℝ) / 1000 * E * ((N - ((b:ℝ) - a) * 10) / N)))) /
          ((b:ℝ) / Dd - (a:ℝ) / Dd) := by
            refine div_le_div_of_nonneg_right ?_ hw.le
            exact add_le_add (mul_le_mul_of_nonneg_left hA hy) (mul_le_mul_of_nonneg_left hB hx)
      _ = SC * ((A:ℝ) / 1000) * (E * ((((b:ℝ) / Dd - v) * ((N + ((b:ℝ) - a) * 10) / N) +
          (v - (a:ℝ) / Dd) * ((N - ((b:ℝ) - a) * 10) / N)) / ((b:ℝ) / Dd - (a:ℝ) / Dd))) := by ring
      _ = SC * ((A:ℝ) / 1000) * (E * (1 - (v - ((a:ℝ) + b) / (2 * Dd)) / ((S:ℝ) / 10))) := by
          rw [hlin]
      _ ≤ SC * ((A:ℝ) / 1000) * Real.exp (-(v / ((S:ℝ) / 10))) :=
          mul_le_mul_of_nonneg_left htan (by positivity)
      _ = _ := by ring
  · have hf : Nat.ble ((b - a) * 10) (2 * Dd * S) = false := by
      rw [Bool.eq_false_iff]; exact fun hh => hc (Nat.le_of_ble_eq_true hh)
    unfold wtA wtB
    rw [hf, cond_false, cond_false]
    simp only [Nat.cast_zero, mul_zero, add_zero, zero_div]
    positivity

/-- linear minorant of `w` on a cell -/
theorem w_minorant (a b wa wb : ℕ) (hab : a < b) (hwa : wa ≤ wA a b) (hwb : wb ≤ wB a b) (v : ℝ)
    (hva : (a:ℝ) / Dd ≤ v) (hvb : v ≤ (b:ℝ) / Dd) :
    (((b:ℝ) / Dd - v) * ((wa:ℝ) / SC) + (v - (a:ℝ) / Dd) * ((wb:ℝ) / SC)) /
      ((b:ℝ) / Dd - (a:ℝ) / Dd) ≤ wf aR sR v := by
  have hSC := SC_pos
  have hD := Dd_pos
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  have hw : (0:ℝ) < (b:ℝ) / Dd - (a:ℝ) / Dd := by
    rw [← sub_div]; exact div_pos (by linarith) hD
  have hy : 0 ≤ (b:ℝ) / Dd - v := by linarith
  have hx : 0 ≤ v - (a:ℝ) / Dd := by linarith
  have h0 := term_minorant (AN 0) (SN 0) a b (SN_pos 0) hab v hva hvb
  have h1 := term_minorant (AN 1) (SN 1) a b (SN_pos 1) hab v hva hvb
  have h2 := term_minorant (AN 2) (SN 2) a b (SN_pos 2) hab v hva hvb
  have h3 := term_minorant (AN 3) (SN 3) a b (SN_pos 3) hab v hva hvb
  have hA : (wa:ℝ) ≤ wtA (AN 0) (SN 0) a b + wtA (AN 1) (SN 1) a b + wtA (AN 2) (SN 2) a b
      + wtA (AN 3) (SN 3) a b := by
    have : (wa:ℝ) ≤ (wA a b : ℕ) := by exact_mod_cast hwa
    unfold wA at this; push_cast at this; exact this
  have hB : (wb:ℝ) ≤ wtB (AN 0) (SN 0) a b + wtB (AN 1) (SN 1) a b + wtB (AN 2) (SN 2) a b
      + wtB (AN 3) (SN 3) a b := by
    have : (wb:ℝ) ≤ (wB a b : ℕ) := by exact_mod_cast hwb
    unfold wB at this; push_cast at this; exact this
  have key : (((b:ℝ) / Dd - v) * (wa:ℝ) + (v - (a:ℝ) / Dd) * (wb:ℝ)) /
      ((b:ℝ) / Dd - (a:ℝ) / Dd) ≤ SC * wf aR sR v := by
    refine (div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hA hy)
      (mul_le_mul_of_nonneg_left hB hx)) hw.le).trans ?_
    unfold wf aR sR
    rw [Fin.sum_univ_four]
    have e : ∀ A0 A1 A2 A3 B0 B1 B2 B3 p q r : ℝ,
        (p * (A0 + A1 + A2 + A3) + q * (B0 + B1 + B2 + B3)) / r =
        (p * A0 + q * B0) / r + (p * A1 + q * B1) / r + (p * A2 + q * B2) / r
          + (p * A3 + q * B3) / r := by intros; ring
    rw [e]
    linarith
  have e : (((b:ℝ) / Dd - v) * ((wa:ℝ) / SC) + (v - (a:ℝ) / Dd) * ((wb:ℝ) / SC)) /
      ((b:ℝ) / Dd - (a:ℝ) / Dd) = (((b:ℝ) / Dd - v) * (wa:ℝ) + (v - (a:ℝ) / Dd) * (wb:ℝ)) /
      ((b:ℝ) / Dd - (a:ℝ) / Dd) / SC := by ring
  rw [e, div_le_iff₀ hSC]
  linarith

theorem avt_le (A S b : ℕ) (hS : 0 < S) (hb : 0 < b) : (avt A S b : ℝ) ≤
    SC * ((A:ℝ) / 1000 * ((S:ℝ) / 10) * (1 - Real.exp (-(((b:ℝ) / Dd) / ((S:ℝ) / 10)))) /
      ((b:ℝ) / Dd)) := by
  have hSC := SC_pos
  have hD := Dd_pos
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hDS : 0 < Dd * S := Nat.mul_pos (by unfold Dd; norm_num) hS
  have he := le_expUp (b * 10) (Dd * S) hDS
  have harg : ((b * 10 : ℕ) : ℝ) / ((Dd * S : ℕ) : ℝ) = ((b:ℝ) / Dd) / ((S:ℝ) / 10) := by
    push_cast; field_simp
  rw [harg] at he
  set e := Real.exp (-(((b:ℝ) / Dd) / ((S:ℝ) / 10))) with hedef
  have he1 : e ≤ 1 := by rw [hedef, Real.exp_le_one_iff, neg_nonpos]; positivity
  have h1 : ((SC - expUp (b * 10) (Dd * S) : ℕ) : ℝ) ≤ SC * (1 - e) := by
    refine (natsub_le _ _).trans (max_le ?_ (mul_nonneg hSC.le (by linarith)))
    linarith
  unfold avt
  refine Nat.cast_div_le.trans ?_
  rw [div_le_iff₀ (by exact_mod_cast Nat.mul_pos (by norm_num) hb)]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  have h2 : (A:ℝ) * S * ((SC - expUp (b * 10) (Dd * S) : ℕ) : ℝ) * Dd ≤
      A * S * (SC * (1 - e)) * Dd :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hD.le
  refine h2.trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

theorem avgLo_le (b av : ℕ) (hb : 0 < b) (hav : av ≤ avgLo b) :
    (av : ℝ) / SC ≤ What aR sR ((b:ℝ) / Dd) / ((b:ℝ) / Dd) := by
  have hSC := SC_pos
  have h0 := avt_le (AN 0) (SN 0) b (SN_pos 0) hb
  have h1 := avt_le (AN 1) (SN 1) b (SN_pos 1) hb
  have h2 := avt_le (AN 2) (SN 2) b (SN_pos 2) hb
  have h3 := avt_le (AN 3) (SN 3) b (SN_pos 3) hb
  have h : (av:ℝ) ≤ (avgLo b : ℕ) := by exact_mod_cast hav
  unfold avgLo at h
  push_cast at h
  rw [div_le_iff₀ hSC]
  unfold What aR sR
  rw [Fin.sum_univ_four, add_div, add_div, add_div]
  linarith

theorem w1_ge : SC * ∑ i, aR i / sR i ≤ (w1 : ℝ) := by
  have hSC := SC_pos
  have h : ∀ i : Fin 4, SC * (aR i / sR i) ≤ (w1t (AN i) (SN i) : ℝ) := by
    intro i
    unfold w1t
    have hS : (0:ℝ) < SN i := by exact_mod_cast SN_pos i
    refine le_trans (le_of_eq ?_) (cdiv_le _ _ (Nat.mul_pos (SN_pos i) (by norm_num)))
    unfold aR sR
    push_cast
    field_simp
  unfold w1
  push_cast
  rw [mul_sum, Fin.sum_univ_four]
  have := h 0; have := h 1; have := h 2; have := h 3
  linarith

theorem aR_sum : ∑ i, aR i = 1 := by
  rw [Fin.sum_univ_four]; unfold aR AN; norm_num

end UB
end Sievert26SimpleAuctions
