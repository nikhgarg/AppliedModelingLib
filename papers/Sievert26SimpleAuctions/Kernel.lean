import Mathlib

/-!
Pure natural-number computations, evaluated by the Lean kernel (GMP-accelerated `Nat`
literals, *no* `native_decide`).  A polynomial `Σ a_k x^k` is packed into the single natural
number obtained by evaluating it at `x = X = 2^s` (Kronecker substitution).
-/
namespace Sievert26SimpleAuctions
namespace Cert

/-- lattice size of the benchmark: the concentrated group has total value `N` -/
def N : ℕ := 400
/-- entry fee -/
def e : ℕ := 580
/-- prefix length -/
def T : ℕ := 2000
def s : ℕ := 30744
def X : ℕ := 2 ^ s
/-- total weight of one item -/
def W : ℕ := 2 ^ 24
/-- total weight of the A-group, `W^(5*256)` -/
def Dn : ℕ := 2 ^ 30720

attribute [irreducible] X Dn

/-- item prices of the five types -/
def P (i : Fin 5) : ℕ := match i with
  | 0 => 8 | 1 => 21 | 2 => 65 | 3 => 132 | 4 => 1280

/-- equal-revenue constants of the five types -/
def R (i : Fin 5) : ℕ := match i with
  | 0 => 1067039 | 1 => 1128540 | 2 => 2129082 | 3 => 2782033 | 4 => 19107703

/-- tail count: `Pr[X ≥ k] = tl r p k / W`. -/
def tl (r p k : ℕ) : ℕ :=
  match k with
  | 0 => W
  | k+1 => cond (Nat.ble (k+1) (p + e)) (r / cond (Nat.ble (k+1) p) p (k+1)) 0

/-- weight of value `k` -/
def cf (r p k : ℕ) : ℕ := tl r p k - tl r p (k+1)

/-- surplus coefficients: value `p+j` has surplus `j`, all values `≤ p` have surplus `0`. -/
def gcoef (r p j : ℕ) : ℕ :=
  match j with
  | 0 => W - tl r p (p+1)
  | j+1 => cf r p (p + (j+1))

/-- `Σ_{j<2^d} c (lo+j) X^j` by divide and conquer. -/
def pack (c : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, lo => c lo
  | d+1, lo => pack c d lo + pack c d (lo + 2^d) * X ^ (2^d)

/-- `Σ_{j<2^d} c (lo+j)` by divide and conquer. -/
def sumTree (c : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, lo => c lo
  | d+1, lo => sumTree c d lo + sumTree c d (lo + 2^d)

/-- `g^(2^k-1) mod M` (for `k ≥ 1`) -/
def pm1 (M g : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => (pm1 M g k * pm1 M g k % M) * g % M

/-- digit `t` in base `X` -/
def digit (F t : ℕ) : ℕ := F / X ^ t % X

/-- loop over the digits of one block, checking the BREV inequality after every digit -/
def inner (F t0 : ℕ) (k : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, C, S => k C S
  | f+1, j, C, S =>
    and (Nat.ble ((N + (t0 + j + 1)) * (Dn - (C + digit F j))) (N * Dn))
      (and (Nat.ble 1 (S + (C + digit F j)))
        (inner F t0 k f (j+1) (C + digit F j) (S + (C + digit F j))))

/-- loop over blocks of 50 digits -/
def outer (F : ℕ) (fin : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, C, S => fin C S
  | f+1, b, C, S =>
    inner (F / X ^ (50 * b) % X ^ 50) (50 * b) (outer F fin f (b+1)) 50 0 C S

/-- packed generating function of one item of type `i` (value) -/
def gA (i : Fin 5) : ℕ := pack (cf (R i) (P i)) 11 0
def MT : ℕ := X ^ T
def pA (i : Fin 5) : ℕ := pm1 MT (gA i) 8 * gA i % MT
/-- packed generating function of the total value of group `A`, modulo `X^T` -/
def FA : ℕ := (((pA 0 * pA 1 % MT) * pA 2 % MT) * pA 3 % MT) * pA 4 % MT

/-- `W * E[one item of type i]` -/
def meanA (i : Fin 5) : ℕ := sumTree (fun k => tl (R i) (P i) (k+1)) 11 0
def EZ : ℕ := 256 * (meanA 0 + meanA 1 + meanA 2 + meanA 3 + meanA 4)

def finalCheck (C S : ℕ) : Bool := Nat.ble (EZ * Dn + W * S) (W * ((N + T) * C))

def brevCheck : Bool := outer FA finalCheck 40 0 0 0

/-- packed generating function of the surplus of one item -/
def gW (i : Fin 5) : ℕ := pack (gcoef (R i) (P i)) 10 0
/-- same, weighted by the item payment -/
def hW (i : Fin 5) : ℕ := pack (fun j => P i * cf (R i) (P i) (P i + j)) 10 0
def Me : ℕ := X ^ e
def q255 (i : Fin 5) : ℕ := pm1 Me (gW i) 8
def q256 (i : Fin 5) : ℕ := q255 i * gW i % Me
def hq (i : Fin 5) : ℕ := 256 * hW i * q255 i % Me
def YW : ℕ :=
  (e * (q256 0 * q256 1 % Me * q256 2 % Me * q256 3 % Me * q256 4 % Me)
  + hq 0 * q256 1 % Me * q256 2 % Me * q256 3 % Me * q256 4
  + q256 0 * hq 1 % Me * q256 2 % Me * q256 3 % Me * q256 4
  + q256 0 * q256 1 % Me * hq 2 % Me * q256 3 % Me * q256 4
  + q256 0 * q256 1 % Me * q256 2 % Me * hq 3 % Me * q256 4
  + q256 0 * q256 1 % Me * q256 2 % Me * q256 3 % Me * hq 4) % Me

def Qloss : ℕ := sumTree (digit YW) 10 0
def payA (i : Fin 5) : ℕ := P i * tl (R i) (P i) (P i)
def EpayNum : ℕ := e * W + 256 * (payA 0 + payA 1 + payA 2 + payA 3 + payA 4)

def revCheck : Bool :=
  Nat.ble (100000 * (W * Qloss) + 119464 * (N * (W * Dn))) (100000 * (EpayNum * Dn))

attribute [irreducible] MT Me gA pA FA gW hW q255 q256 hq YW EZ Qloss EpayNum

end Cert
end Sievert26SimpleAuctions
