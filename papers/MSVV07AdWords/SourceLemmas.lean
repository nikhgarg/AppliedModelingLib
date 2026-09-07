import MSVV07AdWords.MainTheorems
import AppliedModelingLib.Foundations.Optimization.LinearProgram
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.MetricSpace.Basic

/-!
# Source-route lemmas for MSVV07

This file records the source proof-route lemmas from Sections 4 and 5 of
Mehta--Saberi--Vazirani--Vazirani, *AdWords and Generalized Online Matching*.
The main Theorem 8 formalization in `AdWords.lean` uses a direct finite
LP/dual-fitting route; the declarations here make the paper's factor-revealing
and tradeoff-revealing proof steps importable and checkable in Lean.
-/

open scoped BigOperators Topology
open Filter

namespace AppliedModelingLib
namespace Online
namespace MSVV07SourceLemmas

/-! ## Shared finite LP notation -/

/-- Prefix of variables `1, ..., i` in the paper's one-indexed notation. -/
def paperRoutePrefix {m : ℕ} (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun j => j.val ≤ i.val

/-- Paper coefficient `1 + (i-j)/k`, with `k = m + 1` slabs. -/
noncomputable def paperRouteCoeff {m : ℕ} (i j : Fin m) : ℝ :=
  1 + (((i.val : ℝ) - (j.val : ℝ)) / ((m + 1 : ℕ) : ℝ))

/-- The additive part `(i-j)/k` of the paper LP coefficient. -/
noncomputable def paperRouteDeltaCoeff {m : ℕ} (i j : Fin m) : ℝ :=
  ((i.val : ℝ) - (j.val : ℝ)) / ((m + 1 : ℕ) : ℝ)

/-- Paper right-hand side `iN/k`, with Lean's zero-indexed `i`. -/
noncomputable def paperRouteRhs {m : ℕ} (N : ℝ) (i : Fin m) : ℝ :=
  (((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) * N

/-- One row of the factor-revealing LP. -/
noncomputable def paperRouteLPRow {m : ℕ} (x : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j ∈ paperRoutePrefix i, paperRouteCoeff i j * x j

/-- Matrix coefficient for the paper's factor/tradeoff revealing LP family. -/
noncomputable def paperRouteMatrixCoeff {m : ℕ} (i j : Fin m) : ℝ :=
  if j.val ≤ i.val then paperRouteCoeff i j else 0

/-- Suffix of variables `i, ..., k-1` in the paper's one-indexed notation. -/
def paperRouteSuffix {m : ℕ} (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun j => i.val ≤ j.val

/-- Objective coefficient `(k-i)/k` for primal variable `x_i`. -/
noncomputable def paperRoutePrimalObjectiveCoeff {m : ℕ} (i : Fin m) : ℝ :=
  (((m - i.val : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))

/-- Primal objective `c · x` in the factor-revealing LP `L`. -/
noncomputable def paperRoutePrimalObjective {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, paperRoutePrimalObjectiveCoeff i * x i

/-- One dual constraint row `(Aᵀy)_i`. -/
noncomputable def paperRouteDualRow {m : ℕ} (y : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j ∈ paperRouteSuffix i, paperRouteCoeff j i * y j

/-- Dual objective `b · y` in the dual LP `D`. -/
noncomputable def paperRouteDualObjective {m : ℕ} (N : ℝ) (y : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, paperRouteRhs N i * y i

/-- Feasible points of the paper's primal factor-revealing LP `L`. -/
def paperRoutePrimalFeasible {m : ℕ} (N : ℝ) (x : Fin m → ℝ) : Prop :=
  (∀ i, paperRouteLPRow x i ≤ paperRouteRhs N i) ∧ ∀ i, 0 ≤ x i

/-- Feasible points of the paper's dual factor-revealing LP `D`. -/
def paperRouteDualFeasible {m : ℕ} (y : Fin m → ℝ) : Prop :=
  (∀ i, paperRoutePrimalObjectiveCoeff i ≤ paperRouteDualRow y i) ∧
    ∀ i, 0 ≤ y i

/-- The paper's primal candidate `xᵢ* = (N/k)(1 - 1/k)^(i-1)`. -/
noncomputable def paperRoutePrimalCandidate {m : ℕ} (N : ℝ) (i : Fin m) : ℝ :=
  (N / ((m + 1 : ℕ) : ℝ)) *
    (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ i.val

/-- The paper's dual candidate `yᵢ* = (1/k)(1 - 1/k)^(k-i-1)`. -/
noncomputable def paperRouteDualCandidate {m : ℕ} (i : Fin m) : ℝ :=
  (1 / ((m + 1 : ℕ) : ℝ)) *
    (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m - (i.val + 1))

/-- The paper's primal candidate is nonnegative when the total budget is nonnegative. -/
theorem paperRoutePrimalCandidate_nonnegative {m : ℕ} {N : ℝ}
    (hN : 0 ≤ N) (i : Fin m) :
    0 ≤ paperRoutePrimalCandidate (m := m) N i := by
  unfold paperRoutePrimalCandidate
  have hden_pos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hden_nonneg : 0 ≤ (((m + 1 : ℕ) : ℝ)) := hden_pos.le
  have hden_one : (1 : ℝ) ≤ (((m + 1 : ℕ) : ℝ)) := by
    norm_num
  have hfrac_le_one :
      1 / (((m + 1 : ℕ) : ℝ)) ≤ (1 : ℝ) :=
    (div_le_one hden_pos).2 hden_one
  exact
    mul_nonneg (div_nonneg hN hden_nonneg)
      (pow_nonneg (sub_nonneg.2 hfrac_le_one) _)

/-- The paper's dual candidate is nonnegative. -/
theorem paperRouteDualCandidate_nonnegative {m : ℕ} (i : Fin m) :
    0 ≤ paperRouteDualCandidate (m := m) i := by
  unfold paperRouteDualCandidate
  have hden_pos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hden_nonneg : 0 ≤ (((m + 1 : ℕ) : ℝ)) := hden_pos.le
  have hden_one : (1 : ℝ) ≤ (((m + 1 : ℕ) : ℝ)) := by
    norm_num
  have hfrac_le_one :
      1 / (((m + 1 : ℕ) : ℝ)) ≤ (1 : ℝ) :=
    (div_le_one hden_pos).2 hden_one
  exact
    mul_nonneg (div_nonneg zero_le_one hden_nonneg)
      (pow_nonneg (sub_nonneg.2 hfrac_le_one) _)

/-- The paper's closed-form objective value `N(1 - 1/k)^k`. -/
noncomputable def paperRouteCandidateValue (N : ℝ) (k : ℕ) : ℝ :=
  N * (1 - 1 / (k : ℝ)) ^ k

/-- The paper's finite factor-revealing LP `L`. -/
noncomputable def factorRevealingLP (m : ℕ) (N : ℝ) :
    Optimization.StandardMaxLP (Fin m) (Fin m) where
  A := paperRouteMatrixCoeff
  b := paperRouteRhs N
  c := paperRoutePrimalObjectiveCoeff

/-- The paper's tradeoff-revealing LP family, with variable objective/RHS data. -/
noncomputable def tradeoffRevealingLP {m : ℕ}
    (c l : Fin m → ℝ) :
    Optimization.StandardMaxLP (Fin m) (Fin m) where
  A := paperRouteMatrixCoeff
  b := l
  c := c

/-- The factor-revealing LP objective value written with `m = k - 1` variables. -/
noncomputable def factorRevealingLPValue (m : ℕ) (N : ℝ) : ℝ :=
  paperRouteCandidateValue N (m + 1)

/-- The paper prefix set is the finite initial interval in Lean's `Fin` order. -/
theorem paperRoutePrefix_eq_Iic {m : ℕ} (i : Fin m) :
    paperRoutePrefix i = Finset.Iic i := by
  ext j
  simp [paperRoutePrefix]

/-- The paper suffix set is the finite final interval in Lean's `Fin` order. -/
theorem paperRouteSuffix_eq_Ici {m : ℕ} (i : Fin m) :
    paperRouteSuffix i = Finset.Ici i := by
  ext j
  simp [paperRouteSuffix]

/--
The geometric kernel identity behind the paper's displayed primal and dual
factor-revealing LP candidates.
-/
theorem paperRouteKernelSum (K : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (1 + ((n : ℝ) - (j : ℝ)) / K) * (1 - 1 / K) ^ j)
    = (n + 1 : ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let r : ℝ := 1 - 1 / K
      have hgeom :
          (∑ j ∈ Finset.range (n + 1), (1 / K) * r ^ j) =
            1 - r ^ (n + 1) := by
        calc
          (∑ j ∈ Finset.range (n + 1), (1 / K) * r ^ j) =
              ∑ j ∈ Finset.range (n + 1), r ^ j * (1 - r) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [r, mul_comm]
          _ = (∑ j ∈ Finset.range (n + 1), r ^ j) * (1 - r) := by
                rw [Finset.sum_mul]
          _ = 1 - r ^ (n + 1) := by
                exact geom_sum_mul_neg r (n + 1)
      calc
        (∑ j ∈ Finset.range (Nat.succ n + 1),
          (1 + ((Nat.succ n : ℝ) - (j : ℝ)) / K) *
            (1 - 1 / K) ^ j) =
            (∑ j ∈ Finset.range (n + 1),
              (1 + ((n : ℝ) - (j : ℝ)) / K) * r ^ j) +
              (∑ j ∈ Finset.range (n + 1), (1 / K) * r ^ j) +
              r ^ (n + 1) := by
              rw [show Nat.succ n + 1 = n + 1 + 1 by omega]
              rw [Finset.sum_range_succ]
              have hsum :
                  (∑ j ∈ Finset.range (n + 1),
                    (1 + ((Nat.succ n : ℝ) - (j : ℝ)) / K) * r ^ j) =
                    ∑ j ∈ Finset.range (n + 1),
                      ((1 + ((n : ℝ) - (j : ℝ)) / K) * r ^ j +
                        (1 / K) * r ^ j) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                norm_num [Nat.succ_eq_add_one]
                ring
              have hlast :
                  (1 + ((Nat.succ n : ℝ) - ((n + 1 : ℕ) : ℝ)) / K) *
                      (1 - 1 / K) ^ (n + 1) =
                    r ^ (n + 1) := by
                norm_num [Nat.succ_eq_add_one, r]
              simp only [r] at hsum
              rw [hsum]
              rw [hlast]
              rw [Finset.sum_add_distrib]
        _ = (n + 1 : ℝ) + (1 - r ^ (n + 1)) + r ^ (n + 1) := by
              rw [ih]
              rw [hgeom]
        _ = (Nat.succ n + 1 : ℝ) := by
              have hsucc : ((Nat.succ n : ℕ) : ℝ) = (n : ℝ) + 1 := by
                norm_num [Nat.succ_eq_add_one]
              rw [hsucc]
              ring

/--
Weighted geometric value identity used by both displayed candidate objective
calculations in Lemma 3.
-/
theorem paperRouteWeightedGeomValue (m : ℕ) :
    let K : ℝ := ((m + 1 : ℕ) : ℝ)
    let r : ℝ := 1 - 1 / K
    (1 / K) * (1 / K) *
        (∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) * r ^ i)) =
      r ^ (m + 1) := by
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  have hkernel :
      (∑ j ∈ Finset.range (m + 1),
        (1 + ((m : ℝ) - (j : ℝ)) / K) * r ^ j) =
        K := by
    simpa [K, r] using paperRouteKernelSum K m
  have hsplit :
      (∑ j ∈ Finset.range (m + 1),
        (1 + ((m : ℝ) - (j : ℝ)) / K) * r ^ j) =
        (∑ j ∈ Finset.range (m + 1), r ^ j) +
          (1 / K) *
            (∑ j ∈ Finset.range (m + 1), ((m : ℝ) - (j : ℝ)) * r ^ j) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  have hgeom :
      (1 / K) * (∑ j ∈ Finset.range (m + 1), r ^ j) =
        1 - r ^ (m + 1) := by
    calc
      (1 / K) * (∑ j ∈ Finset.range (m + 1), r ^ j) =
          (∑ j ∈ Finset.range (m + 1), r ^ j) * (1 - r) := by
            simp [r, mul_comm]
      _ = 1 - r ^ (m + 1) := by
            exact geom_sum_mul_neg r (m + 1)
  have hweighted_real :
      (1 / K) * (1 / K) *
          (∑ j ∈ Finset.range (m + 1), ((m : ℝ) - (j : ℝ)) * r ^ j) =
        r ^ (m + 1) := by
    calc
      (1 / K) * (1 / K) *
          (∑ j ∈ Finset.range (m + 1), ((m : ℝ) - (j : ℝ)) * r ^ j) =
          (1 / K) *
            ((1 / K) *
              (∑ j ∈ Finset.range (m + 1), ((m : ℝ) - (j : ℝ)) * r ^ j)) := by
            ring
      _ = (1 / K) *
            ((∑ j ∈ Finset.range (m + 1),
              (1 + ((m : ℝ) - (j : ℝ)) / K) * r ^ j) -
              (∑ j ∈ Finset.range (m + 1), r ^ j)) := by
            rw [hsplit]
            ring
      _ = (1 / K) * (K - (∑ j ∈ Finset.range (m + 1), r ^ j)) := by
            rw [hkernel]
      _ = 1 - (1 / K) * (∑ j ∈ Finset.range (m + 1), r ^ j) := by
            simp [K]
            field_simp
      _ = r ^ (m + 1) := by
            rw [hgeom]
            ring
  have hrange :
      (∑ j ∈ Finset.range (m + 1), ((m : ℝ) - (j : ℝ)) * r ^ j) =
        ∑ j ∈ Finset.range m, (((m - j : ℕ) : ℝ) * r ^ j) := by
    rw [Finset.sum_range_succ]
    simp
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjle : j ≤ m := Nat.le_of_lt (Finset.mem_range.mp hj)
    have hcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
      exact Nat.cast_sub hjle
    rw [hcast]
  change (1 / K) * (1 / K) *
      (∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) * r ^ i)) =
    r ^ (m + 1)
  rw [← hrange]
  exact hweighted_real

/-- The paper's primal candidate makes every factor-revealing LP row tight. -/
theorem paperRoutePrimalCandidate_row_tight {m : ℕ} (N : ℝ) (i : Fin m) :
    paperRouteLPRow (paperRoutePrimalCandidate (m := m) N) i =
      paperRouteRhs N i := by
  classical
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  let f : ℕ → ℝ := fun j =>
    (1 + ((i.val : ℝ) - (j : ℝ)) / K) * (N / K * r ^ j)
  have hsum_map :
      (∑ j ∈ Finset.Iic i, f j.val) =
        ∑ j ∈ Finset.range (i.val + 1), f j := by
    have hmap := (Finset.sum_map (Finset.Iic i) Fin.valEmbedding f).symm
    simpa [Fin.map_valEmbedding_Iic, Nat.range_succ_eq_Iic] using hmap
  have hkernel :
      (∑ j ∈ Finset.range (i.val + 1),
        (1 + ((i.val : ℝ) - (j : ℝ)) / K) * r ^ j) =
        (i.val + 1 : ℝ) := by
    simpa [K, r] using paperRouteKernelSum K i.val
  calc
    paperRouteLPRow (paperRoutePrimalCandidate (m := m) N) i =
        ∑ j ∈ Finset.Iic i, f j.val := by
          simp [paperRouteLPRow, paperRoutePrefix_eq_Iic, f,
            paperRouteCoeff, paperRoutePrimalCandidate, K, r]
    _ = ∑ j ∈ Finset.range (i.val + 1), f j := hsum_map
    _ = (N / K) *
        (∑ j ∈ Finset.range (i.val + 1),
          (1 + ((i.val : ℝ) - (j : ℝ)) / K) * r ^ j) := by
          simp [f, Finset.mul_sum, mul_left_comm]
    _ = paperRouteRhs N i := by
          rw [hkernel]
          simp [paperRouteRhs, K]
          ring

/-- The paper's primal candidate is feasible for nonnegative total budget `N`. -/
theorem paperRoutePrimalCandidate_feasible {m : ℕ} {N : ℝ}
    (hN : 0 ≤ N) :
    paperRoutePrimalFeasible (m := m) N
      (paperRoutePrimalCandidate (m := m) N) := by
  refine ⟨?_, paperRoutePrimalCandidate_nonnegative hN⟩
  intro i
  rw [paperRoutePrimalCandidate_row_tight]

/-- The paper's dual candidate makes every factor-revealing dual row tight. -/
theorem paperRouteDualCandidate_row_tight {m : ℕ} (i : Fin m) :
    paperRouteDualRow (paperRouteDualCandidate (m := m)) i =
      paperRoutePrimalObjectiveCoeff (m := m) i := by
  classical
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  let f : ℕ → ℝ := fun j =>
    (1 + ((j : ℝ) - (i.val : ℝ)) / K) *
      ((1 / K) * r ^ (m - (j + 1)))
  let n : ℕ := m - (i.val + 1)
  have hlen : m - i.val = n + 1 := by
    dsimp [n]
    omega
  have hmap :
      (∑ j ∈ Finset.Ici i, f j.val) =
        ∑ j ∈ Finset.Ico i.val m, f j := by
    have hmap := (Finset.sum_map (Finset.Ici i) Fin.valEmbedding f).symm
    simpa [Fin.map_valEmbedding_Ici] using hmap
  have hshift :
      (∑ j ∈ Finset.Ico i.val m, f j) =
        ∑ t ∈ Finset.range (m - i.val), f (i.val + t) := by
    have h := (Finset.sum_Ico_add f 0 (m - i.val) i.val).symm
    simpa [Nat.Ico_zero_eq_range, Nat.sub_add_cancel (Nat.le_of_lt i.isLt),
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hreflect :
      (∑ t ∈ Finset.range (n + 1), f (i.val + t)) =
        ∑ q ∈ Finset.range (n + 1),
          (1 + ((n : ℝ) - (q : ℝ)) / K) * ((1 / K) * r ^ q) := by
    let g : ℕ → ℝ := fun q =>
      (1 + ((n : ℝ) - (q : ℝ)) / K) * ((1 / K) * r ^ q)
    have h := Finset.sum_range_reflect g (n + 1)
    calc
      (∑ t ∈ Finset.range (n + 1), f (i.val + t)) =
          ∑ t ∈ Finset.range (n + 1), g (n + 1 - 1 - t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          have htlt : t < n + 1 := Finset.mem_range.mp ht
          have hsub : n + 1 - 1 - t = n - t := by omega
          have hcoeff : (↑(i.val + t) : ℝ) - (i.val : ℝ) = (t : ℝ) := by
            norm_num
          have hexp : m - (i.val + t + 1) = n - t := by
            dsimp [n]
            omega
          have ht_le : t ≤ n := Nat.le_of_lt_succ htlt
          have hnt_cast : ((n - t : ℕ) : ℝ) = (n : ℝ) - (t : ℝ) :=
            Nat.cast_sub ht_le
          dsimp [f, g]
          rw [hcoeff, hexp, hnt_cast]
          ring
      _ = ∑ q ∈ Finset.range (n + 1), g q := h
      _ = ∑ q ∈ Finset.range (n + 1),
          (1 + ((n : ℝ) - (q : ℝ)) / K) * ((1 / K) * r ^ q) := rfl
  have hkernel :
      (∑ q ∈ Finset.range (n + 1),
        (1 + ((n : ℝ) - (q : ℝ)) / K) * r ^ q) =
        (n + 1 : ℝ) := by
    simpa [K, r] using paperRouteKernelSum K n
  calc
    paperRouteDualRow (paperRouteDualCandidate (m := m)) i =
        ∑ j ∈ Finset.Ici i, f j.val := by
          simp [paperRouteDualRow, paperRouteSuffix_eq_Ici,
            paperRouteCoeff, paperRouteDualCandidate, f, K, r]
    _ = ∑ j ∈ Finset.Ico i.val m, f j := hmap
    _ = ∑ t ∈ Finset.range (m - i.val), f (i.val + t) := hshift
    _ = ∑ t ∈ Finset.range (n + 1), f (i.val + t) := by
          rw [hlen]
    _ = ∑ q ∈ Finset.range (n + 1),
          (1 + ((n : ℝ) - (q : ℝ)) / K) * ((1 / K) * r ^ q) := hreflect
    _ = (1 / K) *
          (∑ q ∈ Finset.range (n + 1),
            (1 + ((n : ℝ) - (q : ℝ)) / K) * r ^ q) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro q hq
          ring
    _ = paperRoutePrimalObjectiveCoeff (m := m) i := by
          rw [hkernel]
          simp [paperRoutePrimalObjectiveCoeff, K, n]
          ring

/-- The paper's dual candidate is feasible. -/
theorem paperRouteDualCandidate_feasible {m : ℕ} :
    paperRouteDualFeasible (m := m)
      (paperRouteDualCandidate (m := m)) := by
  refine ⟨?_, paperRouteDualCandidate_nonnegative⟩
  intro i
  rw [paperRouteDualCandidate_row_tight]

/-- Objective value of the paper's displayed primal candidate. -/
theorem paperRoutePrimalCandidate_objective_value {m : ℕ} (N : ℝ) :
    paperRoutePrimalObjective (m := m)
      (paperRoutePrimalCandidate (m := m) N) =
      factorRevealingLPValue m N := by
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  have hweighted := paperRouteWeightedGeomValue m
  dsimp only at hweighted
  have hweighted' :
      (1 / K) * (1 / K) *
          (∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) * r ^ i)) =
        r ^ (m + 1) := by
    simpa [K, r] using hweighted
  calc
    paperRoutePrimalObjective (m := m)
      (paperRoutePrimalCandidate (m := m) N) =
        ∑ i ∈ Finset.range m,
          (((m - i : ℕ) : ℝ) / K) * (N / K * r ^ i) := by
          change (∑ i : Fin m,
            (((m - i.val : ℕ) : ℝ) / K) * (N / K * r ^ i.val)) =
              ∑ i ∈ Finset.range m,
                (((m - i : ℕ) : ℝ) / K) * (N / K * r ^ i)
          rw [Fin.sum_univ_eq_sum_range
            (fun i : ℕ => (((m - i : ℕ) : ℝ) / K) * (N / K * r ^ i)) m]
    _ = N * (∑ i ∈ Finset.range m,
        (1 / K) * (1 / K) * (((m - i : ℕ) : ℝ) * r ^ i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = N * ((1 / K) * (1 / K) *
        (∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) * r ^ i))) := by
          congr 1
          simp [Finset.mul_sum, mul_left_comm, mul_assoc]
    _ = factorRevealingLPValue m N := by
          rw [hweighted']
          simp [factorRevealingLPValue, paperRouteCandidateValue, K, r]

/-- Objective value of the paper's displayed dual candidate. -/
theorem paperRouteDualCandidate_objective_value {m : ℕ} (N : ℝ) :
    paperRouteDualObjective (m := m) N
      (paperRouteDualCandidate (m := m)) =
      factorRevealingLPValue m N := by
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  have hweighted := paperRouteWeightedGeomValue m
  dsimp only at hweighted
  have hweighted' :
      (1 / K) * (1 / K) *
          (∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) * r ^ i)) =
        r ^ (m + 1) := by
    simpa [K, r] using hweighted
  let f : ℕ → ℝ := fun i =>
    (((i + 1 : ℕ) : ℝ) / K * N) * ((1 / K) * r ^ (m - (i + 1)))
  have hreflect :
      (∑ i ∈ Finset.range m, f i) =
        ∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) / K * N) *
          ((1 / K) * r ^ i) := by
    have h := (Finset.sum_range_reflect f m).symm
    calc
      (∑ i ∈ Finset.range m, f i) =
          ∑ i ∈ Finset.range m, f (m - 1 - i) := h
      _ = ∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) / K * N) *
          ((1 / K) * r ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hlt : i < m := Finset.mem_range.mp hi
          have hsucc : m - 1 - i + 1 = m - i := by omega
          have hexp : m - (m - i) = i := by omega
          dsimp [f]
          rw [hsucc, hexp]
  calc
    paperRouteDualObjective (m := m) N
      (paperRouteDualCandidate (m := m)) =
        ∑ i ∈ Finset.range m, f i := by
          change (∑ i : Fin m,
            (((i.val + 1 : ℕ) : ℝ) / K * N) *
              ((1 / K) * r ^ (m - (i.val + 1)))) =
              ∑ i ∈ Finset.range m, f i
          rw [Fin.sum_univ_eq_sum_range f m]
    _ = ∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) / K * N) *
          ((1 / K) * r ^ i) := hreflect
    _ = N * (∑ i ∈ Finset.range m,
        (1 / K) * (1 / K) * (((m - i : ℕ) : ℝ) * r ^ i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = N * ((1 / K) * (1 / K) *
        (∑ i ∈ Finset.range m, (((m - i : ℕ) : ℝ) * r ^ i))) := by
          congr 1
          simp [Finset.mul_sum, mul_left_comm, mul_assoc]
    _ = factorRevealingLPValue m N := by
          rw [hweighted']
          simp [factorRevealingLPValue, paperRouteCandidateValue, K, r]

/-- The Section 5 perturbation prefix `Δ_i = Σ_{j≤i} (α_j - β_j)`. -/
noncomputable def paperRouteDelta {m : ℕ}
    (alpha beta : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j ∈ paperRoutePrefix i, (alpha j - beta j)

/-- The paper's tradeoff weights induced by a dual vector: `ψ_i = Σ_{j≥i} y_j`. -/
noncomputable def paperRoutePsiFromDual {m : ℕ}
    (y : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j ∈ paperRouteSuffix i, y j

/-- The paper's `ψ` weights induced by the displayed dual candidate `y*`. -/
noncomputable abbrev paperRoutePsiCandidate {m : ℕ} : Fin m → ℝ :=
  paperRoutePsiFromDual (m := m) paperRouteDualCandidate

/-- Closed form for the paper's dual-candidate-induced `ψ` weights. -/
theorem paperRoutePsiCandidate_eq_closed_form {m : ℕ} (i : Fin m) :
    paperRoutePsiCandidate (m := m) i =
      1 - (1 - 1 / (((m + 1 : ℕ) : ℝ))) ^ (m - i.val) := by
  classical
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  let f : ℕ → ℝ := fun j => (1 / K) * r ^ (m - (j + 1))
  let L : ℕ := m - i.val
  have hmap :
      (∑ j ∈ Finset.Ici i, f j.val) =
        ∑ j ∈ Finset.Ico i.val m, f j := by
    have hmap := (Finset.sum_map (Finset.Ici i) Fin.valEmbedding f).symm
    simpa [Fin.map_valEmbedding_Ici] using hmap
  have hshift :
      (∑ j ∈ Finset.Ico i.val m, f j) =
        ∑ t ∈ Finset.range L, f (i.val + t) := by
    have h := (Finset.sum_Ico_add f 0 (m - i.val) i.val).symm
    simpa [L, Nat.Ico_zero_eq_range,
      Nat.sub_add_cancel (Nat.le_of_lt i.isLt), Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using h
  have hreflect :
      (∑ t ∈ Finset.range L, f (i.val + t)) =
        ∑ q ∈ Finset.range L, (1 / K) * r ^ q := by
    let g : ℕ → ℝ := fun q => (1 / K) * r ^ q
    have h := Finset.sum_range_reflect g L
    calc
      (∑ t ∈ Finset.range L, f (i.val + t)) =
          ∑ t ∈ Finset.range L, g (L - 1 - t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          have hexp : m - (i.val + t + 1) = L - 1 - t := by
            dsimp [L]
            omega
          dsimp [f, g]
          rw [hexp]
      _ = ∑ q ∈ Finset.range L, g q := h
      _ = ∑ q ∈ Finset.range L, (1 / K) * r ^ q := rfl
  have hgeom :
      (∑ q ∈ Finset.range L, (1 / K) * r ^ q) =
        1 - r ^ L := by
    calc
      (∑ q ∈ Finset.range L, (1 / K) * r ^ q) =
          ∑ q ∈ Finset.range L, r ^ q * (1 - r) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          simp [r, mul_comm]
      _ = (∑ q ∈ Finset.range L, r ^ q) * (1 - r) := by
          rw [Finset.sum_mul]
      _ = 1 - r ^ L := by
          exact geom_sum_mul_neg r L
  calc
    paperRoutePsiCandidate (m := m) i =
        ∑ j ∈ Finset.Ici i, f j.val := by
          simp [paperRoutePsiCandidate, paperRoutePsiFromDual,
            paperRouteSuffix_eq_Ici, paperRouteDualCandidate, f, K, r]
    _ = ∑ j ∈ Finset.Ico i.val m, f j := hmap
    _ = ∑ t ∈ Finset.range L, f (i.val + t) := hshift
    _ = ∑ q ∈ Finset.range L, (1 / K) * r ^ q := hreflect
    _ = 1 - r ^ L := hgeom
    _ = 1 - (1 - 1 / (((m + 1 : ℕ) : ℝ))) ^ (m - i.val) := by
          simp [L, r, K]

/-- Dual-induced tradeoff weights are antitone whenever the dual vector is nonnegative. -/
theorem paperRoutePsiFromDual_antitone_of_nonnegative {m : ℕ}
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    Antitone (paperRoutePsiFromDual y) := by
  intro i j hij
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro a ha
        simp [paperRouteSuffix] at ha ⊢
        exact le_trans hij ha)
      (by
        intro a _ _
        exact hy a)

/-- The tradeoff weights induced by the paper's dual candidate are antitone. -/
theorem paperRoutePsiFromDualCandidate_antitone {m : ℕ} :
    Antitone (paperRoutePsiFromDual (m := m) paperRouteDualCandidate) := by
  exact
    paperRoutePsiFromDual_antitone_of_nonnegative
      paperRouteDualCandidate paperRouteDualCandidate_nonnegative

theorem paperRouteLPRow_eq_prefix_add_weighted {m : ℕ}
    (x : Fin m → ℝ) (i : Fin m) :
    paperRouteLPRow x i =
      (∑ j ∈ paperRoutePrefix i, x j) +
        ∑ j ∈ paperRoutePrefix i, paperRouteDeltaCoeff i j * x j := by
  simp [paperRouteLPRow, paperRouteCoeff, paperRouteDeltaCoeff, add_mul,
    Finset.sum_add_distrib]

theorem paperRouteMatrixCoeff_row_eq_lpRow {m : ℕ}
    (x : Fin m → ℝ) (i : Fin m) :
    (∑ j : Fin m, paperRouteMatrixCoeff i j * x j) =
      paperRouteLPRow x i := by
  classical
  simp [paperRouteLPRow, paperRoutePrefix, paperRouteMatrixCoeff,
    Finset.sum_filter]

theorem factorRevealingLP_primalObjective_eq {m : ℕ}
    (N : ℝ) (x : Fin m → ℝ) :
    (factorRevealingLP m N).primalObjective x =
      paperRoutePrimalObjective x := by
  rfl

theorem factorRevealingLP_dualObjective_eq {m : ℕ}
    (N : ℝ) (y : Fin m → ℝ) :
    (factorRevealingLP m N).dualObjective y =
      paperRouteDualObjective N y := by
  simp [factorRevealingLP, Optimization.StandardMaxLP.dualObjective,
    paperRouteDualObjective, mul_comm]

theorem factorRevealingLP_primalFeasible_iff {m : ℕ}
    (N : ℝ) (x : Fin m → ℝ) :
    (factorRevealingLP m N).PrimalFeasible x ↔
      paperRoutePrimalFeasible N x := by
  constructor
  · intro hx
    exact ⟨fun i => by
      simpa [factorRevealingLP, paperRouteMatrixCoeff_row_eq_lpRow x i] using hx.2 i,
      hx.1⟩
  · intro hx
    exact ⟨hx.2, fun i => by
      simpa [factorRevealingLP, paperRouteMatrixCoeff_row_eq_lpRow x i] using hx.1 i⟩

theorem factorRevealingLP_dualFeasible_iff {m : ℕ}
    (N : ℝ) (y : Fin m → ℝ) :
    (factorRevealingLP m N).DualFeasible y ↔
      paperRouteDualFeasible y := by
  constructor
  · intro hy
    refine ⟨?_, hy.1⟩
    intro i
    simpa [factorRevealingLP, paperRouteDualRow, paperRouteSuffix,
      paperRouteMatrixCoeff, Finset.sum_filter, mul_comm] using hy.2 i
  · intro hy
    refine ⟨hy.2, ?_⟩
    intro i
    simpa [factorRevealingLP, paperRouteDualRow, paperRouteSuffix,
      paperRouteMatrixCoeff, Finset.sum_filter, mul_comm] using hy.1 i

/--
Finite weak duality for the paper's factor-revealing LP in the source notation.
-/
theorem paperRoute_factor_revealing_weak_duality {m : ℕ}
    (N : ℝ) {x y : Fin m → ℝ}
    (hx : paperRoutePrimalFeasible N x)
    (hy : paperRouteDualFeasible y) :
    paperRoutePrimalObjective x ≤ paperRouteDualObjective N y := by
  have hx' : (factorRevealingLP m N).PrimalFeasible x := by
    simpa [factorRevealingLP_primalFeasible_iff] using hx
  have hy' : (factorRevealingLP m N).DualFeasible y := by
    simpa [factorRevealingLP_dualFeasible_iff] using hy
  simpa [factorRevealingLP_primalObjective_eq,
    factorRevealingLP_dualObjective_eq] using
      (factorRevealingLP m N).weak_duality hx' hy'

/--
Lemma 3, finite LP optimality from the paper's explicit primal/dual certificate.
The geometric closed-form feasibility/value equalities are supplied as the
certificate fields, and weak duality proves the universal upper bound.
-/
noncomputable def lemma3_factor_revealing_lp_optimal_from_certificate {m : ℕ}
    (N : ℝ)
    (hprimal :
      paperRoutePrimalFeasible (m := m) N
        (paperRoutePrimalCandidate (m := m) N))
    (hdual :
      paperRouteDualFeasible (m := m)
        (paperRouteDualCandidate (m := m)))
    (hprimal_value :
      paperRoutePrimalObjective (m := m)
        (paperRoutePrimalCandidate (m := m) N) =
        factorRevealingLPValue m N)
    (hdual_value :
      paperRouteDualObjective (m := m) N
        (paperRouteDualCandidate (m := m)) =
        factorRevealingLPValue m N) :
    Optimization.UpperBoundCertificate
      (α := Fin m → ℝ)
      (paperRoutePrimalFeasible (m := m) N)
      (paperRoutePrimalObjective (m := m))
      (factorRevealingLPValue m N) where
  candidate := paperRoutePrimalCandidate (m := m) N
  candidate_feasible := hprimal
  candidate_value := hprimal_value
  upper_bound := by
    intro x hx
    calc
      paperRoutePrimalObjective (m := m) x ≤
          paperRouteDualObjective (m := m) N
            (paperRouteDualCandidate (m := m)) :=
        paperRoute_factor_revealing_weak_duality N hx hdual
      _ = factorRevealingLPValue m N := hdual_value

/--
Lemma 3, finite LP optimality from row/value certificates for the displayed
`x*` and `y*` witnesses. Nonnegativity of those witnesses is proved here, so
the remaining certificate inputs are exactly the primal rows, dual rows, and
the two objective-value equalities.
-/
noncomputable def lemma3_factor_revealing_lp_optimal_from_row_certificates
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (hprimal_rows :
      ∀ i,
        paperRouteLPRow (paperRoutePrimalCandidate (m := m) N) i ≤
          paperRouteRhs N i)
    (hdual_rows :
      ∀ i,
        paperRoutePrimalObjectiveCoeff (m := m) i ≤
          paperRouteDualRow (paperRouteDualCandidate (m := m)) i)
    (hprimal_value :
      paperRoutePrimalObjective (m := m)
        (paperRoutePrimalCandidate (m := m) N) =
        factorRevealingLPValue m N)
    (hdual_value :
      paperRouteDualObjective (m := m) N
        (paperRouteDualCandidate (m := m)) =
        factorRevealingLPValue m N) :
    Optimization.UpperBoundCertificate
      (α := Fin m → ℝ)
      (paperRoutePrimalFeasible (m := m) N)
      (paperRoutePrimalObjective (m := m))
      (factorRevealingLPValue m N) :=
  lemma3_factor_revealing_lp_optimal_from_certificate
    N
    ⟨hprimal_rows, paperRoutePrimalCandidate_nonnegative hN⟩
    ⟨hdual_rows, paperRouteDualCandidate_nonnegative⟩
    hprimal_value
    hdual_value

/--
Lemma 3, exact finite LP optimality for the paper's displayed geometric
primal and dual candidates. The only semantic side condition is the paper's
nonnegative total budget `N`.
-/
noncomputable def lemma3_factor_revealing_lp_optimal
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    Optimization.UpperBoundCertificate
      (α := Fin m → ℝ)
      (paperRoutePrimalFeasible (m := m) N)
      (paperRoutePrimalObjective (m := m))
      (factorRevealingLPValue m N) :=
  lemma3_factor_revealing_lp_optimal_from_row_certificates
    hN
    (fun i => by
      rw [paperRoutePrimalCandidate_row_tight])
    (fun i => by
      rw [paperRouteDualCandidate_row_tight])
    (paperRoutePrimalCandidate_objective_value N)
    (paperRouteDualCandidate_objective_value N)

/--
Lemma 3, direct optimality statement: the displayed geometric primal witness
maximizes the finite factor-revealing LP.
-/
theorem lemma3_factor_revealing_lp_primal_candidate_is_maximizer
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    Optimization.IsMaximizerOn
      (paperRoutePrimalFeasible (m := m) N)
      (paperRoutePrimalObjective (m := m))
      (paperRoutePrimalCandidate (m := m) N) := by
  exact (lemma3_factor_revealing_lp_optimal (m := m) (N := N) hN).isMaximizerOn

/--
Lemma 3, direct upper-bound statement: every feasible solution of the finite
factor-revealing LP has value at most the paper's closed-form witness value.
-/
theorem lemma3_factor_revealing_lp_upper_bound
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (x : Fin m → ℝ)
    (hx : paperRoutePrimalFeasible (m := m) N x) :
    paperRoutePrimalObjective (m := m) x ≤
      factorRevealingLPValue m N := by
  exact (lemma3_factor_revealing_lp_optimal (m := m) (N := N) hN).upper_bound x hx

/-! ## Topological bridge used by Lemma 3 -/

theorem seqTendsTo_of_tendsto {x : ℕ → ℝ} {L : ℝ}
    (h : Tendsto x atTop (𝓝 L)) :
    Sequence.SeqTendsTo x L := by
  intro δ hδ
  have hball : Metric.ball L δ ∈ 𝓝 L := Metric.ball_mem_nhds _ hδ
  have hevent := h hball
  rw [Filter.mem_map] at hevent
  rw [Filter.mem_atTop_sets] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N, ?_⟩
  intro k hk
  have hkball : x k ∈ Metric.ball L δ := hN k hk
  have hdist : dist (x k) L < δ := by
    simpa [Metric.mem_ball, dist_comm] using hkball
  have habs : |x k - L| < δ := by
    simpa [Real.dist_eq] using hdist
  exact le_of_lt habs

/-! ## Section 4: factor-revealing LP lemmas -/

/--
Lemma 1, source-route form. In the equal-bids BALANCE case, if OPT's bidder is
still active in a slab no later than its final type and BALANCE chooses a
bidder maximizing the equal-bid decreasing slab score, then BALANCE cannot pay
from a later slab.
-/
theorem lemma1_balance_pays_no_later_slab
    {Slab : Type*} [LinearOrder Slab]
    (psi : Slab → ℝ) {optType optCurrentSlab chosenSlab : Slab}
    {bid chosenBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ optType)
    (hchoice :
      bid * psi optCurrentSlab ≤ chosenBid * psi chosenSlab)
    (hequal_bids : chosenBid = bid)
    (hbid_pos : 0 < bid)
    (hpsi_strictAnti : StrictAnti psi) :
    chosenSlab ≤ optType := by
  by_contra hnot
  have htype_lt_chosen : optType < chosenSlab := lt_of_not_ge hnot
  have hcurrent_lt_chosen : optCurrentSlab < chosenSlab :=
    lt_of_le_of_lt hoptCurrent_le_type htype_lt_chosen
  have hpsi_lt : psi chosenSlab < psi optCurrentSlab :=
    hpsi_strictAnti hcurrent_lt_chosen
  have hmul_lt :
      bid * psi chosenSlab < bid * psi optCurrentSlab :=
    mul_lt_mul_of_pos_left hpsi_lt hbid_pos
  rw [hequal_bids] at hchoice
  linarith

/--
Lemma 2. The factor-revealing LP row inequality follows from Lemma 1's prefix
coverage inequality and the paper's slab-spend identity for the same prefix.
-/
theorem lemma2_factor_revealing_lp_constraint
    {m : ℕ} (N : ℝ) (x beta : Fin m → ℝ) (i : Fin m)
    (hprefix_cover :
      (∑ j ∈ paperRoutePrefix i, x j) ≤
        ∑ j ∈ paperRoutePrefix i, beta j)
    (hbeta_prefix :
      (∑ j ∈ paperRoutePrefix i, beta j) =
        paperRouteRhs N i -
          ∑ j ∈ paperRoutePrefix i, paperRouteDeltaCoeff i j * x j) :
    paperRouteLPRow x i ≤ paperRouteRhs N i := by
  calc
    paperRouteLPRow x i =
        (∑ j ∈ paperRoutePrefix i, x j) +
          ∑ j ∈ paperRoutePrefix i, paperRouteDeltaCoeff i j * x j := by
          exact paperRouteLPRow_eq_prefix_add_weighted x i
    _ ≤
        (∑ j ∈ paperRoutePrefix i, beta j) +
          ∑ j ∈ paperRoutePrefix i, paperRouteDeltaCoeff i j * x j := by
          exact add_le_add hprefix_cover le_rfl
    _ = paperRouteRhs N i := by
          rw [hbeta_prefix]
          ring

/--
Lemma 3, exact finite value exposed by the paper's primal/dual candidate:
`Φ_k = N (1 - 1/k)^k` tends to `N/e`.
-/
theorem lemma3_factor_revealing_lp_value_tends (N : ℝ) :
    Sequence.SeqTendsTo
      (fun k : ℕ => N * (1 - 1 / (k : ℝ)) ^ k)
      (N / Real.exp 1) := by
  have hpow :
      Tendsto (fun k : ℕ => (1 - 1 / (k : ℝ)) ^ k) atTop
        (𝓝 (Real.exp (-1))) := by
    have hbase := Real.tendsto_one_add_div_pow_exp (-1)
    refine hbase.congr' ?_
    filter_upwards with k
    ring_nf
  have hmul :
      Tendsto (fun k : ℕ => N * (1 - 1 / (k : ℝ)) ^ k) atTop
        (𝓝 (N * Real.exp (-1))) :=
    tendsto_const_nhds.mul hpow
  have htarget : N * Real.exp (-1) = N / Real.exp 1 := by
    rw [Real.exp_neg]
    ring
  exact seqTendsTo_of_tendsto (by simpa [htarget] using hmul)

/-! ## Section 5: tradeoff-revealing LP lemmas -/

/--
Lemma 4. The paper's complementary-slackness argument is represented by the
standard weak-duality principle: if a feasible primal point and feasible dual
point have equal objective values, the dual point is optimal.
-/
theorem lemma4_dual_optimal_from_primal_dual_match
    {Primal Dual : Type*}
    (primalFeasible : Primal → Prop) (dualFeasible : Dual → Prop)
    (primalObjective : Primal → ℝ) (dualObjective : Dual → ℝ)
    (hweak :
      ∀ primal dual,
        primalFeasible primal → dualFeasible dual →
          primalObjective primal ≤ dualObjective dual)
    {a : Primal} {ystar : Dual}
    (ha : primalFeasible a)
    (_hystar : dualFeasible ystar)
    (hvalue : primalObjective a = dualObjective ystar) :
    ∀ y, dualFeasible y → dualObjective ystar ≤ dualObjective y := by
  intro y hy
  calc
    dualObjective ystar = primalObjective a := hvalue.symm
    _ ≤ dualObjective y := hweak a y ha hy

/--
Lemma 4, finite-LP form. For a standard max LP, a feasible primal point and a
feasible dual point with equal objective values certify dual optimality.
-/
theorem lemma4_standardMaxLP_dual_yStar_optimal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Optimization.StandardMaxLP ι κ)
    {a : ι → ℝ} {ystar : κ → ℝ}
    (ha : P.PrimalFeasible a)
    (hystar : P.DualFeasible ystar)
    (hvalue : P.primalObjective a = P.dualObjective ystar) :
    Optimization.IsMinimizerOn P.DualFeasible P.dualObjective ystar := by
  refine ⟨hystar, ?_⟩
  intro y hy
  calc
    P.dualObjective ystar = P.primalObjective a := hvalue.symm
    _ ≤ P.dualObjective y := P.weak_duality ha hy

/--
Lemma 4's "same constraints" step: changing only the RHS/objective vector `b`
of the dual objective leaves dual feasibility unchanged when `A` and `c` stay
fixed.
-/
theorem lemma4_dual_feasible_of_same_A_c
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b l : κ → ℝ) (c : ι → ℝ)
    {ystar : κ → ℝ}
    (hystar :
      (Optimization.StandardMaxLP.mk A b c).DualFeasible ystar) :
    (Optimization.StandardMaxLP.mk A l c).DualFeasible ystar := by
  simpa [Optimization.StandardMaxLP.DualFeasible] using hystar

/--
Lemma 4 for the paper's factor-revealing matrix.  For each realized
nonnegative type-count vector `a`, the tradeoff-revealing LP has right-hand
side `A a`; the fixed geometric dual candidate is optimal for its dual.
-/
theorem lemma4_paper_tradeoff_dual_candidate_optimal
    {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Optimization.IsMinimizerOn
      (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff
        (fun row => ∑ i : Fin m, paperRouteMatrixCoeff row i * a i)).DualFeasible
      (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff
        (fun row => ∑ i : Fin m, paperRouteMatrixCoeff row i * a i)).dualObjective
      paperRouteDualCandidate := by
  let l : Fin m → ℝ := fun row => ∑ i : Fin m, paperRouteMatrixCoeff row i * a i
  let P : Optimization.StandardMaxLP (Fin m) (Fin m) :=
    tradeoffRevealingLP paperRoutePrimalObjectiveCoeff l
  have hprimal : P.PrimalFeasible a := by
    constructor
    · exact ha
    · intro row
      change (∑ i : Fin m, paperRouteMatrixCoeff row i * a i) ≤
        ∑ i : Fin m, paperRouteMatrixCoeff row i * a i
      exact le_rfl
  have hcolumn : ∀ i : Fin m,
      (∑ row : Fin m, paperRouteMatrixCoeff row i * paperRouteDualCandidate row) =
        paperRoutePrimalObjectiveCoeff i := by
    intro i
    simpa [paperRouteDualRow, paperRouteSuffix, paperRouteMatrixCoeff,
      Finset.sum_filter, mul_comm] using paperRouteDualCandidate_row_tight i
  have hdual : P.DualFeasible paperRouteDualCandidate := by
    constructor
    · exact paperRouteDualCandidate_nonnegative
    · intro i
      change paperRoutePrimalObjectiveCoeff i ≤
        ∑ row : Fin m, paperRouteMatrixCoeff row i * paperRouteDualCandidate row
      exact le_of_eq (hcolumn i).symm
  apply lemma4_standardMaxLP_dual_yStar_optimal P hprimal hdual
  calc
    P.primalObjective a = ∑ i : Fin m, paperRoutePrimalObjectiveCoeff i * a i := by
      rfl
    _ = ∑ i : Fin m,
        (∑ row : Fin m, paperRouteMatrixCoeff row i * paperRouteDualCandidate row) * a i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcolumn i]
    _ = ∑ i : Fin m, ∑ row : Fin m,
        paperRouteMatrixCoeff row i * paperRouteDualCandidate row * a i := by
      simp_rw [Finset.sum_mul]
    _ = ∑ row : Fin m, ∑ i : Fin m,
        paperRouteMatrixCoeff row i * paperRouteDualCandidate row * a i := by
      exact Finset.sum_comm
    _ = ∑ row : Fin m,
        (∑ i : Fin m, paperRouteMatrixCoeff row i * a i) * paperRouteDualCandidate row := by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = P.dualObjective paperRouteDualCandidate := by
      simp [P, l, tradeoffRevealingLP, Optimization.StandardMaxLP.dualObjective,
        mul_comm]

/--
Lemma 5. The right-hand side of the tradeoff-revealing LP is the original
factor-revealing right-hand side plus the perturbation vector `Δ(π, ψ)`.
-/
theorem lemma5_tradeoff_rhs_eq_base_add_delta
    {m : ℕ} (N : ℝ) (alpha beta : Fin m → ℝ) (i : Fin m)
    (hbeta_prefix :
      (∑ j ∈ paperRoutePrefix i, beta j) =
        paperRouteRhs N i -
          ∑ j ∈ paperRoutePrefix i,
            paperRouteDeltaCoeff i j * alpha j) :
    paperRouteLPRow alpha i =
      paperRouteRhs N i + paperRouteDelta alpha beta i := by
  rw [paperRouteLPRow_eq_prefix_add_weighted, paperRouteDelta,
    Finset.sum_sub_distrib, hbeta_prefix]
  ring

/--
Lemma 6. For a query whose OPT bidder is still active in a no-later slab, the
Balance/MSVV maximizing rule and monotonicity of the tradeoff function imply
the per-query ALG/OPT tradeoff inequality.
-/
theorem lemma6_per_query_tradeoff
    {Slab : Type*} [Preorder Slab]
    (psi : Slab → ℝ) {queryType optCurrentSlab algSlab : Slab}
    {optBid algBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ queryType)
    (hpsi_antitone : Antitone psi)
    (hoptBid_nonneg : 0 ≤ optBid)
    (hchoice : optBid * psi optCurrentSlab ≤ algBid * psi algSlab) :
    optBid * psi queryType ≤ algBid * psi algSlab := by
  have hpsi : psi queryType ≤ psi optCurrentSlab :=
    hpsi_antitone hoptCurrent_le_type
  exact (mul_le_mul_of_nonneg_left hpsi hoptBid_nonneg).trans hchoice

/--
Lemma 7. Summing Lemma 6 over all relevant queries and using the paper's type
and slab accounting identities bounds the weighted perturbation by the final
slab error `N/k`.
-/
theorem lemma7_weighted_perturbation_bound
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (finalSlabError : ℝ)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        (∑ i : m, psi i * beta i) + finalSlabError) :
    (∑ i : m, psi i * (alpha i - beta i)) ≤ finalSlabError := by
  have hsum_le :
      (∑ q : Query, opt q * psi (queryType q)) ≤
        ∑ q : Query, alg q * psi (querySlab q) := by
    have hsum_sub :
        (∑ q : Query,
          (opt q * psi (queryType q) - alg q * psi (querySlab q))) =
          (∑ q : Query, opt q * psi (queryType q)) -
            ∑ q : Query, alg q * psi (querySlab q) := by
      rw [Finset.sum_sub_distrib]
    linarith
  have hweighted :
      (∑ i : m, psi i * alpha i) ≤
        (∑ i : m, psi i * beta i) + finalSlabError := by
    rw [← hopt_accounting]
    exact hsum_le.trans halg_accounting
  have hdiff :
      (∑ i : m, psi i * (alpha i - beta i)) =
        (∑ i : m, psi i * alpha i) -
          ∑ i : m, psi i * beta i := by
    simp [mul_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  linarith

/--
Lemma 7, paper-shaped corollary. Once the final-slab error is bounded by the
paper's `N/k` term, the weighted perturbation is bounded by `N/k`.
-/
theorem lemma7_weighted_perturbation_bound_by_N_div_k
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (finalSlabError N : ℝ) (k : ℕ)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        (∑ i : m, psi i * beta i) + finalSlabError)
    (hfinal :
      finalSlabError ≤ N / (k : ℝ)) :
    (∑ i : m, psi i * (alpha i - beta i)) ≤ N / (k : ℝ) := by
  exact
    (lemma7_weighted_perturbation_bound
      psi alpha beta opt alg queryType querySlab finalSlabError
      htradeoff_sum hopt_accounting halg_accounting).trans hfinal

/--
Lemma 7, exact paper-shaped `N/k` form. If the last-slab accounting is already
expressed with the paper's `N/k` term, no extra error variable is exposed.
-/
theorem lemma7_weighted_perturbation_bound_exact_N_div_k
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (N : ℝ) (k : ℕ)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting_N_div_k :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        (∑ i : m, psi i * beta i) + N / (k : ℝ)) :
    (∑ i : m, psi i * (alpha i - beta i)) ≤ N / (k : ℝ) := by
  exact
    lemma7_weighted_perturbation_bound
      psi alpha beta opt alg queryType querySlab (N / (k : ℝ))
      htradeoff_sum hopt_accounting halg_accounting_N_div_k

/-- Lemma 7 helper: pointwise query tradeoff inequalities sum to the global one. -/
theorem lemma7_tradeoff_sum_of_pointwise
    {Query : Type*} [Fintype Query] (w : Query → ℝ)
    (h : ∀ q, w q ≤ 0) :
    (∑ q : Query, w q) ≤ 0 := by
  exact Finset.sum_nonpos fun q _ => h q

/--
Lemma 7 helper: if `alpha i` is the OPT revenue over the fiber of queries of
type `i`, then the weighted OPT query sum equals `Σ_i ψ_i α_i`.
-/
theorem lemma7_opt_accounting_of_type_fibers
    {m Query : Type*} [Fintype m] [Fintype Query] [DecidableEq m]
    (psi alpha : m → ℝ) (opt : Query → ℝ) (queryType : Query → m)
    (hα :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), opt q) = alpha i) :
    (∑ q : Query, opt q * psi (queryType q)) =
      ∑ i : m, psi i * alpha i := by
  classical
  calc
    (∑ q : Query, opt q * psi (queryType q)) =
        ∑ q : Query, psi (queryType q) * opt q := by
          simp [mul_comm]
    _ = ∑ i : m,
        ∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), psi (queryType q) * opt q := by
          rw [Finset.sum_fiberwise]
    _ = ∑ i : m,
        ∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), psi i * opt q := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro q hq
          have hqi : queryType q = i := by
            simpa using (Finset.mem_filter.mp hq).2
          rw [hqi]
    _ = ∑ i : m, psi i *
        ∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), opt q := by
          simp [Finset.mul_sum]
    _ = ∑ i : m, psi i * alpha i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hα i]

/--
Lemma 7 helper: slab-fiber upper bounds on ALG revenue imply the weighted ALG
accounting inequality, up to an explicit nonnegative final-slab error term.
-/
theorem lemma7_alg_accounting_of_slab_fibers_and_final_error
    {m Query : Type*} [Fintype m] [Fintype Query] [DecidableEq m]
    (psi beta : m → ℝ) (alg : Query → ℝ)
    (querySlab : Query → m) (finalSlabError : ℝ)
    (hpsi_nonneg : ∀ i, 0 ≤ psi i)
    (hβ :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => querySlab q = i), alg q) ≤ beta i)
    (hfinal_nonneg : 0 ≤ finalSlabError) :
    (∑ q : Query, alg q * psi (querySlab q)) ≤
      (∑ i : m, psi i * beta i) + finalSlabError := by
  classical
  have hweighted :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        ∑ i : m, psi i * beta i := by
    calc
      (∑ q : Query, alg q * psi (querySlab q)) =
          ∑ q : Query, psi (querySlab q) * alg q := by
            simp [mul_comm]
      _ = ∑ i : m,
          ∑ q ∈ (Finset.univ : Finset Query).filter
            (fun q => querySlab q = i), psi (querySlab q) * alg q := by
            rw [Finset.sum_fiberwise]
      _ = ∑ i : m,
          ∑ q ∈ (Finset.univ : Finset Query).filter
            (fun q => querySlab q = i), psi i * alg q := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro q hq
            have hqi : querySlab q = i := by
              simpa using (Finset.mem_filter.mp hq).2
            rw [hqi]
      _ = ∑ i : m, psi i *
          ∑ q ∈ (Finset.univ : Finset Query).filter
            (fun q => querySlab q = i), alg q := by
            simp [Finset.mul_sum]
      _ ≤ ∑ i : m, psi i * beta i := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact mul_le_mul_of_nonneg_left (hβ i) (hpsi_nonneg i)
  exact hweighted.trans (le_add_of_nonneg_right hfinal_nonneg)

/--
Theorem 8 algebraic route: the dual-weighted perturbation vector is exactly
the weighted `α - β` sum after defining `ψ_i = Σ_{j≥i} y_j`.
-/
theorem theorem8_delta_dot_y_eq_weighted_perturbation
    {m : ℕ} (alpha beta y : Fin m → ℝ) :
    (∑ i : Fin m, y i * paperRouteDelta alpha beta i) =
      ∑ i : Fin m,
        paperRoutePsiFromDual y i * (alpha i - beta i) := by
  classical
  have hleft :
      (∑ i : Fin m, y i * paperRouteDelta alpha beta i) =
        ∑ i : Fin m, ∑ j : Fin m,
          if j.val ≤ i.val then y i * (alpha j - beta j) else 0 := by
    calc
      (∑ i : Fin m, y i * paperRouteDelta alpha beta i) =
          ∑ i : Fin m,
            y i * (∑ j : Fin m,
              if j.val ≤ i.val then alpha j - beta j else 0) := by
            simp only [paperRouteDelta, paperRoutePrefix, Finset.sum_filter]
      _ = ∑ i : Fin m, ∑ j : Fin m,
            y i * (if j.val ≤ i.val then alpha j - beta j else 0) := by
            simp [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ j : Fin m,
            if j.val ≤ i.val then y i * (alpha j - beta j) else 0 := by
            simp [mul_ite]
  have hright :
      (∑ i : Fin m,
        paperRoutePsiFromDual y i * (alpha i - beta i)) =
        ∑ j : Fin m, ∑ i : Fin m,
          if j.val ≤ i.val then y i * (alpha j - beta j) else 0 := by
    calc
      (∑ i : Fin m,
          paperRoutePsiFromDual y i * (alpha i - beta i)) =
          ∑ i : Fin m,
            (∑ j : Fin m, if i.val ≤ j.val then y j else 0) *
              (alpha i - beta i) := by
            simp only [paperRoutePsiFromDual, paperRouteSuffix, Finset.sum_filter]
      _ = ∑ i : Fin m, ∑ j : Fin m,
            (if i.val ≤ j.val then y j else 0) * (alpha i - beta i) := by
            simp [Finset.sum_mul]
      _ = ∑ j : Fin m, ∑ i : Fin m,
            if j.val ≤ i.val then y i * (alpha j - beta j) else 0 := by
            simp [ite_mul]
  rw [hleft, hright, Finset.sum_comm]

/--
Theorem 8 source-route algebraic identity: after writing the perturbed
right-hand side as `l = b + Δ`, the dual objective splits into the base
factor-LP dual value plus the dual-induced weighted perturbation.
-/
theorem theorem8_source_route_dual_value_eq_base_add_perturb
    {m : ℕ} (N : ℝ)
    (alpha beta y l : Fin m → ℝ)
    (hl :
      ∀ i, l i = paperRouteRhs N i + paperRouteDelta alpha beta i) :
    (∑ i : Fin m, l i * y i) =
      paperRouteDualObjective N y +
        ∑ i : Fin m, paperRoutePsiFromDual y i * (alpha i - beta i) := by
  have hdecomp :
      (∑ i : Fin m, l i * y i) =
        paperRouteDualObjective N y +
          ∑ i : Fin m, y i * paperRouteDelta alpha beta i := by
    calc
      (∑ i : Fin m, l i * y i) =
          ∑ i : Fin m,
            (paperRouteRhs N i + paperRouteDelta alpha beta i) * y i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hl i]
      _ = ∑ i : Fin m,
            (paperRouteRhs N i * y i +
              paperRouteDelta alpha beta i * y i) := by
            simp [add_mul]
      _ = paperRouteDualObjective N y +
            ∑ i : Fin m, y i * paperRouteDelta alpha beta i := by
            simp [paperRouteDualObjective, Finset.sum_add_distrib, mul_comm]
  calc
    (∑ i : Fin m, l i * y i) =
        paperRouteDualObjective N y +
          ∑ i : Fin m, y i * paperRouteDelta alpha beta i := hdecomp
    _ = paperRouteDualObjective N y +
        ∑ i : Fin m, paperRoutePsiFromDual y i * (alpha i - beta i) := by
          rw [theorem8_delta_dot_y_eq_weighted_perturbation alpha beta y]

/--
Theorem 8 source-route algebra. If the tradeoff LP right-hand side is
`l = b + Δ`, the Section 4 base dual value is at most `N/e`, and Lemma 7 gives
the `N/k` perturbation bound for the dual-induced weights, then the
tradeoff-revealing dual value is at most `N/e + N/k`.
-/
theorem theorem8_source_route_dual_value_bound
    {m : ℕ} (N : ℝ) (k : ℕ)
    (alpha beta y l : Fin m → ℝ)
    (hl :
      ∀ i, l i = paperRouteRhs N i + paperRouteDelta alpha beta i)
    (hbase :
      paperRouteDualObjective N y ≤ N / Real.exp 1)
    (hperturb :
      (∑ i : Fin m,
        paperRoutePsiFromDual y i * (alpha i - beta i)) ≤
          N / (k : ℝ)) :
    (∑ i : Fin m, l i * y i) ≤ N / Real.exp 1 + N / (k : ℝ) := by
  rw [theorem8_source_route_dual_value_eq_base_add_perturb N alpha beta y l hl]
  exact add_le_add hbase hperturb

/--
Theorem 8 source-route exact finite base bound for the displayed dual
candidate `y*`: no asymptotic `N/e` base assumption is needed before taking
the paper's limit.
-/
theorem theorem8_source_route_dual_candidate_value_bound_exact_base
    {m : ℕ} (N : ℝ) (k : ℕ)
    (alpha beta l : Fin m → ℝ)
    (hl :
      ∀ i, l i = paperRouteRhs N i + paperRouteDelta alpha beta i)
    (hperturb :
      (∑ i : Fin m,
        paperRoutePsiCandidate i * (alpha i - beta i)) ≤ N / (k : ℝ)) :
    (∑ i : Fin m, l i * paperRouteDualCandidate i) ≤
      factorRevealingLPValue m N + N / (k : ℝ) := by
  rw [theorem8_source_route_dual_value_eq_base_add_perturb
    N alpha beta paperRouteDualCandidate l hl]
  rw [paperRouteDualCandidate_objective_value N]
  exact add_le_add le_rfl (by simpa [paperRoutePsiCandidate] using hperturb)

/--
The displayed dual candidate `y*` is feasible for the tradeoff-revealing LP
whenever the objective coefficients are the paper's factor-LP coefficients.
-/
theorem theorem8_source_route_dual_candidate_tradeoff_feasible
    {m : ℕ} (l : Fin m → ℝ) :
    (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).DualFeasible
      paperRouteDualCandidate := by
  have hy : paperRouteDualFeasible (m := m) paperRouteDualCandidate :=
    paperRouteDualCandidate_feasible
  constructor
  · exact hy.2
  · intro i
    simpa [tradeoffRevealingLP, paperRouteDualRow, paperRouteSuffix,
      paperRouteMatrixCoeff, Finset.sum_filter, mul_comm] using hy.1 i

/--
Theorem 8 source-route LP upper bound. The source-route dual-value bound,
together with finite weak duality for the tradeoff-revealing LP, upper-bounds
the objective of every feasible tradeoff-LP primal point by `N/e + N/k`.
-/
theorem theorem8_source_route_tradeoff_lp_upper_bound
    {m : ℕ} (N : ℝ) (k : ℕ)
    (c alpha beta y l : Fin m → ℝ)
    (hy : (tradeoffRevealingLP c l).DualFeasible y)
    (hl :
      ∀ i, l i = paperRouteRhs N i + paperRouteDelta alpha beta i)
    (hbase :
      paperRouteDualObjective N y ≤ N / Real.exp 1)
    (hperturb :
      (∑ i : Fin m,
        paperRoutePsiFromDual y i * (alpha i - beta i)) ≤
          N / (k : ℝ))
    {x : Fin m → ℝ}
    (hx : (tradeoffRevealingLP c l).PrimalFeasible x) :
    (tradeoffRevealingLP c l).primalObjective x ≤
      N / Real.exp 1 + N / (k : ℝ) := by
  have hdual :
      (tradeoffRevealingLP c l).dualObjective y ≤
        N / Real.exp 1 + N / (k : ℝ) := by
    calc
      (tradeoffRevealingLP c l).dualObjective y =
          ∑ i : Fin m, l i * y i := by
          simp [tradeoffRevealingLP, Optimization.StandardMaxLP.dualObjective,
            mul_comm]
      _ ≤ N / Real.exp 1 + N / (k : ℝ) :=
          theorem8_source_route_dual_value_bound
            N k alpha beta y l hl hbase hperturb
  exact ((tradeoffRevealingLP c l).weak_duality hx hy).trans hdual

/--
Theorem 8 source-route exact finite LP upper bound using the displayed dual
candidate `y*` and the exact finite Section 4 base value.
-/
theorem theorem8_source_route_tradeoff_lp_upper_bound_exact_base
    {m : ℕ} (N : ℝ) (k : ℕ)
    (alpha beta l : Fin m → ℝ)
    (hl :
      ∀ i, l i = paperRouteRhs N i + paperRouteDelta alpha beta i)
    (hperturb :
      (∑ i : Fin m,
        paperRoutePsiCandidate i * (alpha i - beta i)) ≤ N / (k : ℝ))
    {x : Fin m → ℝ}
    (hx :
      (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).PrimalFeasible
        x) :
    (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).primalObjective x ≤
      factorRevealingLPValue m N + N / (k : ℝ) := by
  have hy := theorem8_source_route_dual_candidate_tradeoff_feasible (m := m) l
  have hdual :
      (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).dualObjective
          paperRouteDualCandidate ≤
        factorRevealingLPValue m N + N / (k : ℝ) := by
    calc
      (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).dualObjective
          paperRouteDualCandidate =
          ∑ i : Fin m, l i * paperRouteDualCandidate i := by
          simp [tradeoffRevealingLP, Optimization.StandardMaxLP.dualObjective,
            mul_comm]
      _ ≤ factorRevealingLPValue m N + N / (k : ℝ) :=
          theorem8_source_route_dual_candidate_value_bound_exact_base
            N k alpha beta l hl hperturb
  exact
    ((tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).weak_duality
      hx hy).trans hdual

/--
Theorem 8 source-route accounting wrapper: Lemma 7's query accounting
hypotheses feed directly into the exact finite tradeoff-LP upper bound for
the displayed dual candidate.
-/
theorem theorem8_source_route_tradeoff_lp_upper_bound_from_query_accounting
    {m : ℕ} {Query : Type*} [Fintype Query]
    (N : ℝ) (k : ℕ)
    (alpha beta l : Fin m → ℝ)
    (opt alg : Query → ℝ)
    (queryType querySlab : Query → Fin m)
    (hl :
      ∀ i, l i = paperRouteRhs N i + paperRouteDelta alpha beta i)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * paperRoutePsiCandidate (queryType q) -
          alg q * paperRoutePsiCandidate (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * paperRoutePsiCandidate (queryType q)) =
        ∑ i : Fin m, paperRoutePsiCandidate i * alpha i)
    (halg_accounting_N_div_k :
      (∑ q : Query, alg q * paperRoutePsiCandidate (querySlab q)) ≤
        (∑ i : Fin m, paperRoutePsiCandidate i * beta i) + N / (k : ℝ))
    {x : Fin m → ℝ}
    (hx :
      (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).PrimalFeasible
        x) :
    (tradeoffRevealingLP (m := m) paperRoutePrimalObjectiveCoeff l).primalObjective x ≤
      factorRevealingLPValue m N + N / (k : ℝ) := by
  have hperturb :
      (∑ i : Fin m,
        paperRoutePsiCandidate i * (alpha i - beta i)) ≤ N / (k : ℝ) :=
    lemma7_weighted_perturbation_bound_exact_N_div_k
      paperRoutePsiCandidate alpha beta opt alg queryType querySlab
      N k htradeoff_sum hopt_accounting halg_accounting_N_div_k
  exact
    theorem8_source_route_tradeoff_lp_upper_bound_exact_base
      N k alpha beta l hl hperturb hx

end MSVV07SourceLemmas
end Online
end AppliedModelingLib
