/-!
Integer checker for the upper-bound certificate (pure `ℕ`, evaluated by the Lean kernel).
Mirrors `code/ub_certificate.py`.  Lengths are in units `1/Dd`, real numbers are scaled by `SC`.
-/
namespace Sievert26SimpleAuctions
namespace UBCert

def SC : Nat := 1000000000000
def Dd : Nat := 10000
def Dx : Nat := 1000
def UN : Nat := 1000000

def cdiv (a b : Nat) : Nat := (a + b - 1) / b

def sqLo (S : Nat) : Nat → Nat → Nat
  | 0, y => y
  | k+1, y => sqLo S k (y * y / S)
def sqUp (S : Nat) : Nat → Nat → Nat
  | 0, y => y
  | k+1, y => sqUp S k (cdiv (y * y) S)
def polyLo (x : Nat) : Nat := (SC + x * x / (2 * SC)) - (x + cdiv (x * x * x) (6 * SC * SC))
def polyUp (x : Nat) : Nat := (SC + cdiv (x * x) (2 * SC)) - x
def ek (a b : Nat) : Nat := Nat.log2 (a / b) + 7
/-- lower bound of `SC·exp(-a/b)` -/
def expLo (a b : Nat) : Nat := sqLo SC (ek a b) (polyLo (cdiv (a * SC) (b * 2 ^ ek a b)))
/-- upper bound of `SC·exp(-a/b)` -/
def expUp (a b : Nat) : Nat := sqUp SC (ek a b) (polyUp (a * SC / (b * 2 ^ ek a b)))
/-- upper bound of `SC·ψ(al/v)` -/
def psiUp (al v : Nat) : Nat := SC + cdiv (v * expUp al v) al - SC * v / al

/-- kernel weights (sum 1000) and scales (in tenths) -/
def AN (i : Fin 4) : Nat := match i with
  | 0 => 266 | 1 => 509 | 2 => 203 | 3 => 22
def SN (i : Fin 4) : Nat := match i with
  | 0 => 5 | 1 => 14 | 2 => 220 | 3 => 2093

/-- one term of the linear minorant of `w` on `[a,b]`, at the left / right end -/
def wtA (A S a b : Nat) : Nat :=
  cond (Nat.ble ((b - a) * 10) (2 * Dd * S))
    (A * expLo ((a + b) * 10) (2 * Dd * S) * (2 * Dd * S + (b - a) * 10) / (1000 * (2 * Dd * S))) 0
def wtB (A S a b : Nat) : Nat :=
  cond (Nat.ble ((b - a) * 10) (2 * Dd * S))
    (A * expLo ((a + b) * 10) (2 * Dd * S) * (2 * Dd * S - (b - a) * 10) / (1000 * (2 * Dd * S))) 0
def wA (a b : Nat) : Nat :=
  wtA (AN 0) (SN 0) a b + wtA (AN 1) (SN 1) a b + wtA (AN 2) (SN 2) a b + wtA (AN 3) (SN 3) a b
def wB (a b : Nat) : Nat :=
  wtB (AN 0) (SN 0) a b + wtB (AN 1) (SN 1) a b + wtB (AN 2) (SN 2) a b + wtB (AN 3) (SN 3) a b
def avt (A S b : Nat) : Nat := A * S * (SC - expUp (b * 10) (Dd * S)) * Dd / (10000 * b)
/-- lower bound of `SC·What(t)/t` at `t = b/Dd` -/
def avgLo (b : Nat) : Nat :=
  avt (AN 0) (SN 0) b + avt (AN 1) (SN 1) b + avt (AN 2) (SN 2) b + avt (AN 3) (SN 3) b
def w1t (A S : Nat) : Nat := cdiv (A * 10 * SC) (S * 1000)
def w1 : Nat := w1t (AN 0) (SN 0) + w1t (AN 1) (SN 1) + w1t (AN 2) (SN 2) + w1t (AN 3) (SN 3)

/-- a cell `[a,b]`: left end `a`, minorant values `wa, wb`, lower bound `av` of the average at `b` -/
abbrev Cell := Nat × Nat × Nat × Nat

/-- validity of the table (descending list of cells, starting below `b`) -/
def tabOk : List Cell → Nat → Bool
  | [], _ => true
  | (a, wa, wb, av) :: rest, b =>
    and (Nat.ble 1 a) (and (Nat.ble (a + 1) b) (and (Nat.ble wa (wA a b))
      (and (Nat.ble wb (wB a b)) (and (Nat.ble av (avgLo b)) (tabOk rest a)))))

/-- cell integral bound -/
def cellI (a b la lb : Nat) : Nat :=
  cdiv ((b - a) * (2 * la * b + la * a + lb * b + 2 * lb * a)) (6 * a * b)

/-- scan the cells from the right; `G` bounds the integral from `b` on -/
def levLoop (al ts te ka g : Nat) : List Cell → Nat → Nat → Nat → Bool
  | [], b, _, G =>
    cond (Nat.ble b ts) true
      (and (Nat.beq ts 0) (Nat.ble (ka + (G + cdiv (w1 * b) Dd)) (g + avgLo b)))
  | (a, wa, wb, av) :: rest, b, pb, G =>
    cond (Nat.ble b ts) true
      (and (Nat.ble 0 (G + cellI a b (psiUp al a - wa) (pb - wb)))
        (and (cond (Nat.ble te a) true
            (Nat.ble (ka + (G + cellI a b (psiUp al a - wa) (pb - wb))) (g + av)))
          (levLoop al ts te ka g rest a (psiUp al a)
            (G + cellI a b (psiUp al a - wa) (pb - wb)))))

def tail0 (al Vmax : Nat) : Nat := cdiv (SC * al) (2 * Vmax)

def lev (tab : List Cell) (Vmax kap g al ts te : Nat) : Bool :=
  levLoop al ts te (cdiv (kap * Dd) al) g tab Vmax (psiUp al Vmax) (tail0 al Vmax)

/-- all levels; `levels` lists the later `(start, alpha)` -/
def allLev (tab : List Cell) (Vmax kap g : Nat) : Nat → Nat → List (Nat × Nat) → Bool
  | ts, al, [] => and (Nat.ble (cdiv (kap * Dd) al + tail0 al Vmax) g)
      (lev tab Vmax kap g al ts Vmax)
  | ts, al, (ts', al') :: rest =>
    and (Nat.ble al al') (and (Nat.ble ts' Vmax) (and (lev tab Vmax kap g al ts ts')
      (allLev tab Vmax kap g ts' al' rest)))

/-! ### tangents -/
def om (y0n y0d p q : Nat) : Nat := expLo (y0n * (p + q)) (y0d * (2 * Dx)) * Dx * (q - p) / (p * q)

def tanLoop (y0n y0d bn kn : Nat) : List Nat → Nat → Nat → Nat → Bool
  | [], _, Q, M =>
    and (Nat.ble (M * UN) (bn * Q * (2 * Dx)))
      (Nat.ble (expUp (kn * y0d + bn * y0n) (UN * y0d) * UN * y0d * (2 * Dx)
        + y0n * (bn * Q * (2 * Dx) - M * UN)) (Q * UN * y0d * (2 * Dx)))
  | q :: rest, p, Q, M =>
    and (Nat.ble (p + 1) q) (and (Nat.ble 0 (Q + om y0n y0d p q))
      (and (Nat.ble 0 (M + om y0n y0d p q * (p + q)))
      (tanLoop y0n y0d bn kn rest q (Q + om y0n y0d p q) (M + om y0n y0d p q * (p + q)))))

end UBCert
end Sievert26SimpleAuctions
