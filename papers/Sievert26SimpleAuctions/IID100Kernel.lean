/-!
Pure natural-number kernel checks for the 100-item i.i.d. lower bound (`>= 1.324907`,
Proposition 5). Uses Horner packing, repeated squaring, modular truncation mod `X^9`,
and a shifting loop checked inside the Lean kernel (`decide +kernel`, no `native_decide`).
-/
namespace Sievert26SimpleAuctions
namespace IID100Cert

/-- Weights of the values `0, …, 13` (sum `3003000`), realizing
`Pr[X >= k] = 3 / (25 * max(k, 4))` for `1 <= k <= 13` and `0` for `k > 13`. -/
def cN (k : Nat) : Nat := match k with
  | 0 => 2912910 | 4 => 18018 | 5 => 12012 | 6 => 8580 | 7 => 6435 | 8 => 5005
  | 9 => 4004 | 10 => 3276 | 11 => 2730 | 12 => 2310 | 13 => 27720 | _ => 0

def W : Nat := 3003000

/-- Fast binary powering for `a^9`, `a^99`, `a^100`, and `a^99 mod M`. -/
def pow9 (a : Nat) : Nat :=
  let a2 := a * a
  let a4 := a2 * a2
  let a8 := a4 * a4
  a8 * a

def pow99 (a : Nat) : Nat :=
  let a2 := a * a
  let a3 := a2 * a
  let a4 := a2 * a2
  let a8 := a4 * a4
  let a16 := a8 * a8
  let a32 := a16 * a16
  let a64 := a32 * a32
  a64 * a32 * a3

def pow100 (a : Nat) : Nat :=
  let a2 := a * a
  let a4 := a2 * a2
  let a8 := a4 * a4
  let a16 := a8 * a8
  let a32 := a16 * a16
  let a64 := a32 * a32
  a64 * a32 * a4

def pow99Mod (M a : Nat) : Nat :=
  let a1 := a % M
  let a2 := a1 * a1 % M
  let a3 := a2 * a1 % M
  let a4 := a2 * a2 % M
  let a8 := a4 * a4 % M
  let a16 := a8 * a8 % M
  let a32 := a16 * a16 % M
  let a64 := a32 * a32 % M
  (a64 * a32 % M) * a3 % M

def X : Nat := 2 ^ 2200
def Dn : Nat := pow100 W
def W99 : Nat := pow99 W
def Me : Nat := pow9 X

def gz : Nat :=
  let h :=
    ((((((((cN 13 * X + cN 12) * X + cN 11) * X + cN 10) * X + cN 9) * X + cN 8) * X + cN 7) * X
      + cN 6) * X + cN 5) * X + cN 4
  let x2 := X * X
  let x4 := x2 * x2
  h * x4 + cN 0

/-- Surplus generating function (item price `4`). -/
def gw : Nat :=
  ((((((((cN 13 * X + cN 12) * X + cN 11) * X + cN 10) * X + cN 9) * X + cN 8) * X + cN 7) * X
    + cN 6) * X + cN 5) * X + (cN 0 + cN 4)

def hw : Nat :=
  4 * ((((((((cN 13 * X + cN 12) * X + cN 11) * X + cN 10) * X + cN 9) * X + cN 8) * X + cN 7) * X
    + cN 6) * X + cN 5) * X + 4 * cN 4

def Fz : Nat := pow100 gz

def gw99M : Nat := pow99Mod Me gw
def gw100M : Nat := gw99M * gw % Me
def YwM : Nat := (9 * gw100M + 100 * (hw * gw99M % Me)) % Me

/-- Shifting loop: `cur` holds `F / X^t`. Checks `t * (Dn - C) * 10^6 <= 12065329 * Dn`. -/
def loop (X Dn : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | f+1, t, C, cur =>
    and (Nat.ble (t * (Dn - C) * 1000000) (12065329 * Dn))
      (loop X Dn f (t+1) (C + cur % X) (cur / X))

def brevCheck : Bool := loop X Dn 1301 0 0 Fz

def sumDigits (X : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, cur => cur % X + sumDigits X k (cur / X)

def qloss : Nat := sumDigits X 9 YwM

/-- Total weight of `9 + payments` is `(9 W + 100 * 4 * 90090) W^99`.
Checks expected revenue `>= 15985442 / 1000000`. -/
def revCheck : Bool :=
  Nat.ble (15985442 * Dn + 1000000 * qloss) (1000000 * ((9 * W + 400 * 90090) * W99))

theorem W_pos_nat : 0 < W := by decide +kernel
theorem W_val : 25 * 360360 = 3 * W := by decide +kernel
theorem bound_X : (9 * W + 400 * 90090) * W99 < X := by decide +kernel
theorem Dn_lt_X : Dn < X := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem brevCheck_true : brevCheck = true := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem revCheck_true : revCheck = true := by decide +kernel

attribute [irreducible] W X Dn W99 Me gz gw hw Fz gw99M gw100M YwM qloss

end IID100Cert
end Sievert26SimpleAuctions
