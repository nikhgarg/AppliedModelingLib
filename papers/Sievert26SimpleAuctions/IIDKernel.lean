/-!
Pure natural-number kernel checks for the 40-item iid lower bound (`> 1.316 · max(SREV, BREV)`).
Uses Horner packing, repeated squaring, modular truncation mod `X^9`, and a shifting loop so
every `decide +kernel` check runs in a few seconds inside the Lean kernel (no `native_decide`).
-/
namespace Sievert26SimpleAuctions
namespace IIDCert

/-- weights of the values `0,…,13` (sum `3603600`) -/
def cN (k : Nat) : Nat := match k with
  | 0 => 3333330 | 4 => 54054 | 5 => 36036 | 6 => 25740 | 7 => 19305 | 8 => 15015
  | 9 => 12012 | 10 => 9828 | 11 => 8190 | 12 => 6930 | 13 => 83160 | _ => 0

def W : Nat := 3603600

/-- Fast binary powering for `2^900`, `a^40`, `a^39`, `a^9`. -/
def pow9 (a : Nat) : Nat :=
  let a2 := a * a
  let a4 := a2 * a2
  let a8 := a4 * a4
  a8 * a

def pow39 (a : Nat) : Nat :=
  let a2 := a * a
  let a3 := a2 * a
  let a4 := a2 * a2
  let a7 := a4 * a3
  let a8 := a4 * a4
  let a16 := a8 * a8
  let a32 := a16 * a16
  a32 * a7

def pow40 (a : Nat) : Nat :=
  let a2 := a * a
  let a4 := a2 * a2
  let a8 := a4 * a4
  let a16 := a8 * a8
  let a32 := a16 * a16
  a32 * a8

def pow39Mod (M a : Nat) : Nat :=
  let a1 := a % M
  let a2 := a1 * a1 % M
  let a3 := a2 * a1 % M
  let a4 := a2 * a2 % M
  let a7 := a4 * a3 % M
  let a8 := a4 * a4 % M
  let a16 := a8 * a8 % M
  let a32 := a16 * a16 % M
  a32 * a7 % M

def X : Nat := 2 ^ 900
def Dn : Nat := pow40 W
def W39 : Nat := pow39 W
def Me : Nat := pow9 X

def gz : Nat :=
  let h :=
    ((((((((cN 13 * X + cN 12) * X + cN 11) * X + cN 10) * X + cN 9) * X + cN 8) * X + cN 7) * X
      + cN 6) * X + cN 5) * X + cN 4
  let x2 := X * X
  let x4 := x2 * x2
  h * x4 + cN 0

/-- surplus generating function (item price `4`) -/
def gw : Nat :=
  ((((((((cN 13 * X + cN 12) * X + cN 11) * X + cN 10) * X + cN 9) * X + cN 8) * X + cN 7) * X
    + cN 6) * X + cN 5) * X + (cN 0 + cN 4)

def hw : Nat :=
  4 * ((((((((cN 13 * X + cN 12) * X + cN 11) * X + cN 10) * X + cN 9) * X + cN 8) * X + cN 7) * X
    + cN 6) * X + cN 5) * X + 4 * cN 4

def Fz : Nat := pow40 gz

def gw39M : Nat := pow39Mod Me gw
def gw40M : Nat := gw39M * gw % Me
def YwM : Nat := (9 * gw40M + 40 * (hw * gw39M % Me)) % Me

/-- Shifting loop: `cur` holds `F / X^t`. -/
def loop (X Dn : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | f+1, t, C, cur =>
    and (Nat.ble (t * (Dn - C) * 1000) (12151 * Dn))
      (loop X Dn f (t+1) (C + cur % X) (cur / X))

def brevCheck : Bool := loop X Dn 521 0 0 Fz

def sumDigits (X : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, cur => cur % X + sumDigits X k (cur / X)

def qloss : Nat := sumDigits X 9 YwM

/-- total weight of `9 + payments` is `(9 W + 40·4·270270) W^39` -/
def revCheck : Bool := Nat.ble (16 * Dn + qloss) ((9 * W + 160 * 270270) * W39)

theorem W_pos_nat : 0 < W := by decide +kernel
theorem W_val : 10 * 1081080 = 3 * W := by decide +kernel
theorem bound_X : (9 * W + 160 * 270270) * W39 < X := by decide +kernel
theorem Dn_lt_X : Dn < X := by decide +kernel

set_option maxRecDepth 100000 in
theorem brevCheck_true : brevCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem revCheck_true : revCheck = true := by decide +kernel

attribute [irreducible] W X Dn W39 Me gz gw hw Fz gw39M gw40M YwM qloss

end IIDCert
end Sievert26SimpleAuctions
