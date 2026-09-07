import AppliedModelingLib.Foundations.Math.FiniteOptimization
import AppliedModelingLib.Foundations.Math.ExponentialBounds
import AppliedModelingLib.Foundations.Math.Asymptotics
import AppliedModelingLib.Foundations.Math.IntegralConvergence
import AppliedModelingLib.Foundations.Math.MonotoneContinuity
import AppliedModelingLib.Foundations.Math.OrderedPairs
import AppliedModelingLib.Foundations.Math.UniformConvergence
import AppliedModelingLib.Foundations.Optimization.Bisection
import AppliedModelingLib.Foundations.Optimization.Certificate
import AppliedModelingLib.Applications.RatingSystems.BinaryLargeDeviations
import AppliedModelingLib.Foundations.Probability.FiniteMeasurablePartition
import AppliedModelingLib.Foundations.Probability.IntegralLargeDeviations

/-!
# Implementation Theorems: Designing Optimal Binary Rating Systems

This file contains the finite binary-rating, equalized-rate, source-grid, and
large-deviation support used by the paper-facing interface for Garg and Johari
(2019). The reusable Bernoulli/KL, finite optimization, and aggregation layers
are imported from the public library surface above.
-/

open scoped BigOperators

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open AppliedModelingLib.Probability
open Filter Topology
open MeasureTheory

/-- Source KL formula for two Bernoulli success probabilities. -/
def sourceBernoulliKL (a b : ℝ) : ℝ :=
  bernoulliKL a b

/--
Support-safe Bernoulli KL convention. Thresholds outside the Bernoulli support
contribute `⊤`, matching the finite-support convention used by GJ18.
-/
def sourceBernoulliKLTop (a b : ℝ) : WithTop ℝ :=
  if 0 ≤ a ∧ a ≤ 1 then
    (sourceBernoulliKL a b : WithTop ℝ)
  else
    ⊤

/--
Adjacent binary-rating rate
`inf_a {g_hi KL(a || t_hi) + g_lo KL(a || t_lo)}`.
-/
def adjacentBinaryRatingRate
    (gHi gLo tHi tLo : ℝ) : ℝ :=
  sInf (Set.range fun a : ℝ =>
    twoBernoulliThresholdRate gHi gLo tHi tLo a)

/--
Support-safe adjacent binary-rating threshold objective. This is the same
displayed KL objective, but thresholds outside `[0,1]` have extended rate
`⊤` rather than a real-valued formula artifact.
-/
def adjacentBinaryThresholdObjectiveTop
    (gHi gLo tHi tLo a : ℝ) : WithTop ℝ :=
  withTopRealScale gHi (sourceBernoulliKLTop a tHi) +
    withTopRealScale gLo (sourceBernoulliKLTop a tLo)

/-- Support-safe adjacent binary-rating rate. -/
def adjacentBinaryRatingRateTop
    (gHi gLo tHi tLo : ℝ) : WithTop ℝ :=
  sInf (Set.range fun a : ℝ =>
    adjacentBinaryThresholdObjectiveTop gHi gLo tHi tLo a)

/--
The bracketed geometric-arithmetic expression in the closed adjacent binary
rate from Lemma 3.1.
-/
def adjacentBinaryRatingClosedRateBase
    (gLo gHi tLo tHi : ℝ) : ℝ :=
  ((1 - tLo) ^ (gLo / (gLo + gHi))) *
      ((1 - tHi) ^ (gHi / (gLo + gHi))) +
    (tLo ^ (gLo / (gLo + gHi))) *
      (tHi ^ (gHi / (gLo + gHi)))

/--
Closed-form adjacent rate displayed in Lemma 3.1 after minimizing over the
threshold `a`.
-/
def adjacentBinaryRatingClosedRate
    (gLo gHi tLo tHi : ℝ) : ℝ :=
  -(gLo + gHi) *
    Real.log (adjacentBinaryRatingClosedRateBase gLo gHi tLo tHi)

/-- Lower endpoint index for adjacent intervals in a finite binary level chain. -/
abbrev adjacentLowIndex {m : ℕ} (i : Fin (m + 1)) : Fin (m + 2) :=
  Fin.castSucc i

/-- Upper endpoint index for adjacent intervals in a finite binary level chain. -/
abbrev adjacentHighIndex {m : ℕ} (i : Fin (m + 1)) : Fin (m + 2) :=
  i.succ

/-- Closed adjacent rate at interval `i` in a finite binary level chain. -/
def binaryClosedAdjacentRateAt {m : ℕ}
    (g t : Fin (m + 2) → ℝ) (i : Fin (m + 1)) : ℝ :=
  adjacentBinaryRatingClosedRate
    (g (adjacentLowIndex i)) (g (adjacentHighIndex i))
    (t (adjacentLowIndex i)) (t (adjacentHighIndex i))

/-- First level in the finite binary chain. -/
abbrev firstLevelIndex {m : ℕ} : Fin (m + 2) :=
  ⟨0, by omega⟩

/-- Last level in the finite binary chain. -/
abbrev lastLevelIndex {m : ℕ} : Fin (m + 2) :=
  ⟨m + 1, by omega⟩

/-- First adjacent comparison in the finite binary chain. -/
abbrev firstAdjacentIndex {m : ℕ} : Fin (m + 1) :=
  ⟨0, by omega⟩

/-- Last adjacent comparison in the finite binary chain. -/
abbrev lastAdjacentIndex {m : ℕ} : Fin (m + 1) :=
  ⟨m, by omega⟩

/--
Endpoint-aware adjacent rate for a finite binary level chain with source
endpoint convention `t_0 = 0`, `t_last = 1`.  The first and last comparisons
use the simplified endpoint rates; middle comparisons use the closed weighted
Bernoulli rate.
-/
def binaryEndpointAwareAdjacentRate {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) : ℝ :=
  if i.val = 0 then
    sampleRate (adjacentHighIndex i) *
      (-Real.log (1 - successProb (adjacentHighIndex i)))
  else if i.val = m then
    sampleRate (adjacentLowIndex i) *
      (-Real.log (successProb (adjacentLowIndex i)))
  else
    weightedBernoulliClosedThresholdRate
      (sampleRate (adjacentHighIndex i))
      (sampleRate (adjacentLowIndex i))
      (successProb (adjacentHighIndex i))
      (successProb (adjacentLowIndex i))

/--
Endpoint-aware pair rate for a finite binary level chain. This extends the
adjacent convention to a wider ordered pair `(low, high)`: comparisons from
the bottom endpoint use the lower-tail endpoint exponent, comparisons to the
top endpoint use the upper-tail endpoint exponent, and interior comparisons
use the closed weighted two-Bernoulli rate.
-/
def binaryEndpointAwarePairRate {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (low high : Fin (m + 2)) : ℝ :=
  if low.val = 0 then
    sampleRate high * (-Real.log (1 - successProb high))
  else if high.val = m + 1 then
    sampleRate low * (-Real.log (successProb low))
  else
    weightedBernoulliClosedThresholdRate
      (sampleRate high) (sampleRate low)
      (successProb high) (successProb low)

/--
The nontrivial ordered level pairs used in the C.3/Theorem 3.1 decomposition:
strictly ordered level indices, excluding the single bottom-to-top endpoint
comparison.
-/
def theorem31OrderedNontrivialPairSelected {m : ℕ}
    (piece : Fin (m + 2) × Fin (m + 2)) : Prop :=
  piece.1.val + 1 ≤ piece.2.val ∧
    (piece.1.val ≠ 0 ∨ piece.2.val ≠ m + 1)

instance theorem31OrderedNontrivialPairSelected_decidablePred {m : ℕ} :
    DecidablePred (theorem31OrderedNontrivialPairSelected (m := m)) := by
  intro piece
  dsimp [theorem31OrderedNontrivialPairSelected]
  infer_instance

/-- Subtype of nontrivial ordered level pairs used by Theorem 3.1/C.3. -/
abbrev theorem31OrderedNontrivialPairComponent (m : ℕ) :=
  {piece : Fin (m + 2) × Fin (m + 2) //
    theorem31OrderedNontrivialPairSelected (m := m) piece}

/-- Adjacent level pairs are selected nontrivial ordered pairs when there is at
least one interior level. -/
def theorem31OrderedAdjacentPiece {m : ℕ} (hm : 0 < m)
    (adj : Fin (m + 1)) : theorem31OrderedNontrivialPairComponent m :=
  ⟨(adjacentLowIndex adj, adjacentHighIndex adj), by
    constructor
    · simp [adjacentLowIndex, adjacentHighIndex]
    · by_cases hfirst : adj.val = 0
      · right
        simp [adjacentHighIndex, hfirst]
        omega
      · left
        simpa [adjacentLowIndex] using hfirst⟩

/--
The endpoint-aware pair-rate convention agrees with the adjacent-rate convention
on adjacent level pairs.
-/
theorem binaryEndpointAwarePairRate_adjacent_eq_adjacentRate {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (adj : Fin (m + 1)) :
    binaryEndpointAwarePairRate successProb sampleRate
        (adjacentLowIndex adj) (adjacentHighIndex adj) =
      binaryEndpointAwareAdjacentRate successProb sampleRate adj := by
  by_cases hfirst : adj.val = 0
  · simp [binaryEndpointAwarePairRate, binaryEndpointAwareAdjacentRate,
      adjacentLowIndex, adjacentHighIndex, hfirst]
  · by_cases hlast : adj.val = m
    · have hhigh_last : (adjacentHighIndex adj).val = m + 1 := by
        simp [adjacentHighIndex, hlast]
      simp [binaryEndpointAwarePairRate, binaryEndpointAwareAdjacentRate,
        adjacentLowIndex, adjacentHighIndex, hlast]
    · have hlow_not_first : (adjacentLowIndex adj).val ≠ 0 := by
        simpa [adjacentLowIndex] using hfirst
      have hhigh_not_last : (adjacentHighIndex adj).val ≠ m + 1 := by
        simp [adjacentHighIndex]
        omega
      simp [binaryEndpointAwarePairRate, binaryEndpointAwareAdjacentRate,
        hfirst, hlast]

/--
Feasible finite endpoint level vector for Lemma 3.1: the source convention
fixes the first level at `0`, the last at `1`, and adjacent levels strictly
increase.
-/
def BinaryEndpointLevelVector {m : ℕ} (t : Fin (m + 2) → ℝ) : Prop :=
  t (firstLevelIndex : Fin (m + 2)) = 0 ∧
    t (lastLevelIndex : Fin (m + 2)) = 1 ∧
    ∀ i : Fin (m + 1), t (adjacentLowIndex i) < t (adjacentHighIndex i)

/-- Every non-bottom level of an endpoint level vector is positive. -/
theorem BinaryEndpointLevelVector_pos_of_not_first {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    (i : Fin (m + 2)) (hi : i.val ≠ 0) :
    0 < t i := by
  let x : ℕ → ℝ := fun n => if h : n < m + 2 then t ⟨n, h⟩ else 0
  have hstep : ∀ k : ℕ, k < m + 1 → x k < x (k + 1) := by
    intro k hk
    have hk_low : k < m + 2 := by omega
    have hk_high : k + 1 < m + 2 := by omega
    have h := ht.2.2 ⟨k, hk⟩
    simpa [x, adjacentLowIndex, adjacentHighIndex, hk_low, hk_high] using h
  have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
  have hi_le_last : i.val ≤ m + 1 := Nat.le_of_lt_succ i.isLt
  have hchain : x 0 < x i.val := by
    refine AppliedModelingLib.lt_of_adjacent_lt_chain x (i := 0) (j := i.val) hi_pos ?_
    intro k _hk0 hki
    exact hstep k (lt_of_lt_of_le hki hi_le_last)
  have hfirst : x 0 = 0 := by
    have h0 : 0 < m + 2 := by omega
    simpa [x, h0, firstLevelIndex] using ht.1
  have hi_x : x i.val = t i := by
    simpa [x, i.isLt]
  linarith

/-- Every non-top level of an endpoint level vector is below one. -/
theorem BinaryEndpointLevelVector_lt_one_of_not_last {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    (i : Fin (m + 2)) (hi : i.val ≠ m + 1) :
    t i < 1 := by
  let x : ℕ → ℝ := fun n => if h : n < m + 2 then t ⟨n, h⟩ else 0
  have hstep : ∀ k : ℕ, k < m + 1 → x k < x (k + 1) := by
    intro k hk
    have hk_low : k < m + 2 := by omega
    have hk_high : k + 1 < m + 2 := by omega
    have h := ht.2.2 ⟨k, hk⟩
    simpa [x, adjacentLowIndex, adjacentHighIndex, hk_low, hk_high] using h
  have hi_le_last : i.val ≤ m + 1 := Nat.le_of_lt_succ i.isLt
  have hi_lt_last : i.val < m + 1 := lt_of_le_of_ne hi_le_last hi
  have hchain : x i.val < x (m + 1) := by
    refine
      AppliedModelingLib.lt_of_adjacent_lt_chain x (i := i.val) (j := m + 1)
        hi_lt_last ?_
    intro k _hik hklast
    exact hstep k hklast
  have hlast : x (m + 1) = 1 := by
    have hlast_idx : m + 1 < m + 2 := by omega
    simpa [x, hlast_idx, lastLevelIndex] using ht.2.1
  have hi_x : x i.val = t i := by
    simpa [x, i.isLt]
  linarith

/-- Every level of an endpoint level vector is nonnegative. -/
theorem BinaryEndpointLevelVector_nonneg {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    (i : Fin (m + 2)) :
    0 ≤ t i := by
  by_cases hi : i.val = 0
  · have hidx : i = (firstLevelIndex : Fin (m + 2)) := by
      ext
      simpa [firstLevelIndex] using hi
    simpa [hidx] using le_of_eq ht.1.symm
  · exact le_of_lt (BinaryEndpointLevelVector_pos_of_not_first ht i hi)

/-- Every level of an endpoint level vector is at most one. -/
theorem BinaryEndpointLevelVector_le_one {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    (i : Fin (m + 2)) :
    t i ≤ 1 := by
  by_cases hi : i.val = m + 1
  · have hidx : i = (lastLevelIndex : Fin (m + 2)) := by
      ext
      simpa [lastLevelIndex] using hi
    simpa [hidx] using le_of_eq ht.2.1
  · exact le_of_lt (BinaryEndpointLevelVector_lt_one_of_not_last ht i hi)

/-- Adjacent levels of an endpoint level vector are ordered. -/
theorem BinaryEndpointLevelVector_adjacent_ordered {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    (i : Fin (m + 1)) :
    t (adjacentLowIndex i) ≤ t (adjacentHighIndex i) :=
  (ht.2.2 i).le

/-- Endpoint level vectors are monotone in their finite index. -/
theorem BinaryEndpointLevelVector_mono {m : ℕ}
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t)
    {a b : Fin (m + 2)} (hab : a.val ≤ b.val) :
    t a ≤ t b := by
  by_cases hEq : a.val = b.val
  · have hab_eq : a = b := by
      ext
      exact hEq
    subst b
    exact le_rfl
  · have hlt : a.val < b.val := lt_of_le_of_ne hab hEq
    let x : ℕ → ℝ := fun n => if h : n < m + 2 then t ⟨n, h⟩ else 0
    have hstep : ∀ k : ℕ, a.val ≤ k → k < b.val → x k < x (k + 1) := by
      intro k _hak hkb
      have hk : k < m + 1 := by
        have hb_le : b.val ≤ m + 1 := Nat.le_of_lt_succ b.isLt
        omega
      have hk_low : k < m + 2 := by omega
      have hk_high : k + 1 < m + 2 := by omega
      have h := ht.2.2 ⟨k, hk⟩
      simpa [x, adjacentLowIndex, adjacentHighIndex, hk_low, hk_high] using h
    have hchain : x a.val < x b.val :=
      AppliedModelingLib.lt_of_adjacent_lt_chain x hlt hstep
    have ha_x : x a.val = t a := by
      simpa [x, a.isLt]
    have hb_x : x b.val = t b := by
      simpa [x, b.isLt]
    exact le_of_lt (by simpa [ha_x, hb_x] using hchain)

/--
Any level whose index lies between `i` and `i+2` lies in the corresponding
two-step bracket.  This small monotonicity lemma is used to pair an old anchor
level with a refined C.5 level in the B.1 proof.
-/
theorem BinaryEndpointLevelVector_level_mem_two_step_interval_of_index_between
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (i : Fin m) (k : Fin (m + 2))
    (hlo : i.1 ≤ k.1) (hhi : k.1 ≤ i.1 + 2) :
    levels k ∈
      Set.Icc (levels ⟨i.1, by omega⟩)
        (levels ⟨i.1 + 2, by omega⟩) := by
  constructor
  · exact
      BinaryEndpointLevelVector_mono
        (a := (⟨i.1, by omega⟩ : Fin (m + 2))) (b := k)
        hlevels hlo
  · exact
      BinaryEndpointLevelVector_mono
        (a := k) (b := (⟨i.1 + 2, by omega⟩ : Fin (m + 2)))
        hlevels hhi

/--
Finite-chain arithmetic core of Lemma C.6: if the last adjacent interval is
no wider than every adjacent interval, then the last interval width is at most
the reciprocal of the number of adjacent intervals.
-/
theorem BinaryEndpointLevelVector_last_width_le_inv_of_last_width_le_all
    {m : ℕ} {t : Fin (m + 2) → ℝ}
    (ht : BinaryEndpointLevelVector t)
    (hlast_width :
      ∀ i : Fin (m + 1),
        t (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            t (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          t (adjacentHighIndex i) - t (adjacentLowIndex i)) :
    t (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
        t (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
      1 / ((m + 1 : ℕ) : ℝ) := by
  let x : ℕ → ℝ := fun n => if h : n < m + 2 then t ⟨n, h⟩ else 0
  have hx0 : x 0 = 0 := by
    have h0 : 0 < m + 2 := by omega
    simpa [x, h0, firstLevelIndex] using ht.1
  have hxN : x (m + 1) = 1 := by
    have hN : m + 1 < m + 2 := by omega
    simpa [x, hN, lastLevelIndex] using ht.2.1
  have hgap :
      ∀ k : ℕ, k < m + 1 →
        x (m + 1) - x ((m + 1) - 1) ≤ x (k + 1) - x k := by
    intro k hk
    have hk_low : k < m + 2 := by omega
    have hk_high : k + 1 < m + 2 := by omega
    have hm_low : m < m + 2 := by omega
    have hm_high : m + 1 < m + 2 := by omega
    have h := hlast_width ⟨k, hk⟩
    simpa [x, hk_low, hk_high, hm_low, hm_high,
      lastAdjacentIndex, adjacentLowIndex, adjacentHighIndex] using h
  have h :=
    AppliedModelingLib.last_gap_le_inv_of_last_gap_le_all
      x (n := m + 1) (by omega) hx0 hxN hgap
  have hm_low : m < m + 2 := by omega
  have hm_high : m + 1 < m + 2 := by omega
  simpa [x, hm_low, hm_high, lastAdjacentIndex,
    adjacentLowIndex, adjacentHighIndex] using h

/--
Lemma C.6 arithmetic bridge in level form: if the last adjacent interval is no
wider than every adjacent interval, then the penultimate level is at least
`1 - 1 / (number of adjacent intervals)`.
-/
theorem BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_last_width_le_all
    {m : ℕ} {t : Fin (m + 2) → ℝ}
    (ht : BinaryEndpointLevelVector t)
    (hlast_width :
      ∀ i : Fin (m + 1),
        t (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            t (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          t (adjacentHighIndex i) - t (adjacentLowIndex i)) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      t (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
  have hwidth :=
    BinaryEndpointLevelVector_last_width_le_inv_of_last_width_le_all
      ht hlast_width
  have hlast_one :
      t (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) = 1 := by
    simpa [lastAdjacentIndex, adjacentHighIndex, lastLevelIndex] using ht.2.1
  linarith

/-- The C.6 reciprocal lower bound is positive whenever there is an interior level. -/
theorem one_sub_inv_adjacent_count_pos {m : ℕ} (hm : 0 < m) :
    0 < 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
  have hn_gt_one : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < m + 1)
  have hinv_lt : 1 / ((m + 1 : ℕ) : ℝ) < 1 := by
    have h :=
      one_div_lt_one_div_of_lt (a := (1 : ℝ))
        (b := ((m + 1 : ℕ) : ℝ)) zero_lt_one hn_gt_one
    simpa using h
  linarith

/-- For at least two adjacent intervals, the C.6 lower bound is at least `1/2`. -/
theorem one_half_le_one_sub_inv_adjacent_count {m : ℕ} (hm : 0 < m) :
    (1 / 2 : ℝ) ≤ 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
  have htwo_le : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ m + 1)
  have hinv_le : 1 / ((m + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo_le
  linarith

/-- The first interior level of an endpoint level vector is below the top endpoint. -/
theorem BinaryEndpointLevelVector_first_high_lt_one {m : ℕ} (hm : 0 < m)
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t) :
    t (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) < 1 := by
  let x : ℕ → ℝ := fun n => if h : n < m + 2 then t ⟨n, h⟩ else 0
  have hstep : ∀ k : ℕ, k < m + 1 → x k < x (k + 1) := by
    intro k hk
    have hk_low : k < m + 2 := by omega
    have hk_high : k + 1 < m + 2 := by omega
    have h := ht.2.2 ⟨k, hk⟩
    simpa [x, adjacentLowIndex, adjacentHighIndex, hk_low, hk_high] using h
  have hchain : x 1 < x (m + 1) := by
    refine AppliedModelingLib.lt_of_adjacent_lt_chain x (i := 1) (j := m + 1) (by omega) ?_
    intro k _hk1 hkj
    exact hstep k (by omega)
  have hlast : x (m + 1) = 1 := by
    have hlast_idx : m + 1 < m + 2 := by omega
    simpa [x, hlast_idx, lastLevelIndex] using ht.2.1
  have hfirst_high : x 1 =
      t (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
    have h1 : 1 < m + 2 := by omega
    simp [x, h1, firstAdjacentIndex, adjacentHighIndex]
  linarith

/-- The last interior level of an endpoint level vector is above the bottom endpoint. -/
theorem BinaryEndpointLevelVector_last_low_pos {m : ℕ} (hm : 0 < m)
    {t : Fin (m + 2) → ℝ} (ht : BinaryEndpointLevelVector t) :
    0 < t (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
  let x : ℕ → ℝ := fun n => if h : n < m + 2 then t ⟨n, h⟩ else 0
  have hstep : ∀ k : ℕ, k < m + 1 → x k < x (k + 1) := by
    intro k hk
    have hk_low : k < m + 2 := by omega
    have hk_high : k + 1 < m + 2 := by omega
    have h := ht.2.2 ⟨k, hk⟩
    simpa [x, adjacentLowIndex, adjacentHighIndex, hk_low, hk_high] using h
  have hchain : x 0 < x m := by
    refine AppliedModelingLib.lt_of_adjacent_lt_chain x (i := 0) (j := m) (by omega) ?_
    intro k _hk0 hkm
    exact hstep k (by omega)
  have hfirst : x 0 = 0 := by
    have h0 : 0 < m + 2 := by omega
    simpa [x, h0, firstLevelIndex] using ht.1
  have hlast_low : x m =
      t (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
    have hm_lt : m < m + 2 := by omega
    simp [x, hm_lt, lastAdjacentIndex, adjacentLowIndex]
  linarith

/-- First adjacent endpoint-aware rate branch. -/
theorem binaryEndpointAwareAdjacentRate_first {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hi : i.val = 0) :
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      sampleRate (adjacentHighIndex i) *
        (-Real.log (1 - successProb (adjacentHighIndex i))) := by
  simp [binaryEndpointAwareAdjacentRate, hi]

/-- Last adjacent endpoint-aware rate branch. -/
theorem binaryEndpointAwareAdjacentRate_last {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val = m) :
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      sampleRate (adjacentLowIndex i) *
        (-Real.log (successProb (adjacentLowIndex i))) := by
  have hm_ne : m ≠ 0 := by
    intro hm
    exact hfirst (by omega)
  simp [binaryEndpointAwareAdjacentRate, hlast, hm_ne]

/-- Interior adjacent endpoint-aware rate branch. -/
theorem binaryEndpointAwareAdjacentRate_interior {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m) :
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      weightedBernoulliClosedThresholdRate
        (sampleRate (adjacentHighIndex i))
        (sampleRate (adjacentLowIndex i))
        (successProb (adjacentHighIndex i))
      (successProb (adjacentLowIndex i)) := by
  simp [binaryEndpointAwareAdjacentRate, hfirst, hlast]

/--
Uniform endpoint comparison for the source Theorem 3.2 first-rate invariant.
For uniform sample rates, `r(last) ≤ r(first)` follows from the endpoint
mirror inequality `1 - t₁ ≤ t_{last-low}`.
-/
theorem binaryEndpointAwareAdjacentRate_uniform_last_le_first_of_one_sub_first_high_le_last_low
    {m : ℕ} (hm : 0 < m)
    (successProb : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hmirror :
      1 -
          successProb
            (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤
        successProb
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointAwareAdjacentRate successProb
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin (m + 1)) ≤
      binaryEndpointAwareAdjacentRate successProb
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (firstAdjacentIndex : Fin (m + 1)) := by
  let first : Fin (m + 1) := firstAdjacentIndex
  let last : Fin (m + 1) := lastAdjacentIndex
  let firstHigh : Fin (m + 2) := adjacentHighIndex first
  let lastLow : Fin (m + 2) := adjacentLowIndex last
  have hfirstHigh_lt_one : successProb firstHigh < 1 := by
    have hnot_last : firstHigh.val ≠ m + 1 := by
      simp [firstHigh, first]
      omega
    exact BinaryEndpointLevelVector_lt_one_of_not_last hlevels firstHigh hnot_last
  have hlastLow_pos : 0 < successProb lastLow := by
    have hnot_first : lastLow.val ≠ 0 := by
      simp [lastLow, last]
      omega
    exact BinaryEndpointLevelVector_pos_of_not_first hlevels lastLow hnot_first
  have hcomp_pos : 0 < 1 - successProb firstHigh := by
    linarith
  have hlog :
      Real.log (1 - successProb firstHigh) ≤ Real.log (successProb lastLow) :=
    Real.log_le_log hcomp_pos hmirror
  have hlast_formula :
      binaryEndpointAwareAdjacentRate successProb
          (fun _ : Fin (m + 2) => (1 : ℝ)) last =
        -Real.log (successProb lastLow) := by
    have hfirst_last : last.val ≠ 0 := by
      simp [last]
      omega
    have hlast_last : last.val = m := by
      simp [last]
    simpa [lastLow] using
      binaryEndpointAwareAdjacentRate_last
        successProb (fun _ : Fin (m + 2) => (1 : ℝ)) last
        hfirst_last hlast_last
  have hfirst_formula :
      binaryEndpointAwareAdjacentRate successProb
          (fun _ : Fin (m + 2) => (1 : ℝ)) first =
        -Real.log (1 - successProb firstHigh) := by
    have hfirst_first : first.val = 0 := by
      simp [first]
    simpa [firstHigh] using
      binaryEndpointAwareAdjacentRate_first
        successProb (fun _ : Fin (m + 2) => (1 : ℝ)) first
        hfirst_first
  rw [hlast_formula, hfirst_formula]
  linarith

/--
Interior `BisectNextLevel` bridge: if the lower endpoint of an interior
adjacent interval is selected by the reusable low-endpoint inverse-rate
selector, then the corresponding endpoint-aware adjacent rate is at most the
target rate.
-/
theorem binaryEndpointAwareAdjacentRate_interior_lowEndpointOfRateOrFloor_le_target
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    {floor target : ℝ}
    (hgHi : 0 < sampleRate (adjacentHighIndex i))
    (hgLo : 0 < sampleRate (adjacentLowIndex i))
    (hfloor0 : 0 < floor)
    (hfloor_le_hi : floor ≤ successProb (adjacentHighIndex i))
    (hhi1 : successProb (adjacentHighIndex i) < 1)
    (htarget_pos : 0 < target)
    (hselected :
      successProb (adjacentLowIndex i) =
        weightedBernoulliLowEndpointOfRateOrFloor
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          floor
          (successProb (adjacentHighIndex i))
          target) :
    binaryEndpointAwareAdjacentRate successProb sampleRate i ≤ target := by
  rw [binaryEndpointAwareAdjacentRate_interior successProb sampleRate i hfirst hlast,
    hselected]
  exact
    weightedBernoulliClosedThresholdRate_lowEndpointOfRateOrFloor_le_target
      hgHi hgLo hfloor0 hfloor_le_hi hhi1 htarget_pos

/--
Interior `BisectNextLevel` quantitative bridge: if the returned lower endpoint
is the upper endpoint of a bisection bracket around the exact low-endpoint
root for a target closed rate, then the returned adjacent rate is no smaller
than the target rate minus the logarithmic grid-shift loss.
-/
theorem binaryEndpointAwareAdjacentRate_interior_ge_target_sub_low_shift_log_of_bisection_bracket
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    {root lower delta target : ℝ}
    (hgHi : 0 ≤ sampleRate (adjacentHighIndex i))
    (hgLo : 0 ≤ sampleRate (adjacentLowIndex i))
    (hGpos :
      0 <
        sampleRate (adjacentHighIndex i) +
          sampleRate (adjacentLowIndex i))
    (hhi0 : 0 < successProb (adjacentHighIndex i))
    (hhi1 : successProb (adjacentHighIndex i) < 1)
    (hroot0 : 0 < root)
    (hreturned1 : successProb (adjacentLowIndex i) < 1)
    (hroot_rate :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (successProb (adjacentHighIndex i)) root =
        target)
    (B :
      AppliedModelingLib.Optimization.RealBisectionBracket
        root lower (successProb (adjacentLowIndex i)) delta) :
    target -
        sampleRate (adjacentLowIndex i) *
          Real.log ((root + delta) / root) ≤
      binaryEndpointAwareAdjacentRate successProb sampleRate i := by
  have hshift :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (successProb (adjacentHighIndex i)) root -
          sampleRate (adjacentLowIndex i) *
            Real.log ((root + delta) / root) ≤
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (successProb (adjacentHighIndex i))
          (successProb (adjacentLowIndex i)) := by
    exact
      weightedBernoulliClosedThresholdRate_low_shift_ge_sub_log_add_div
        hgHi hgLo hGpos hhi0 hhi1 hroot0 B.target_le_upper
        B.upper_le_target_add_delta hreturned1
  rw [binaryEndpointAwareAdjacentRate_interior successProb sampleRate i hfirst hlast]
  simpa [hroot_rate] using hshift

/--
Interior `BisectNextLevel` grid bridge in the source Theorem 3.2 form: if the
exact low-endpoint root is at least `tFirst`, then the local logarithmic loss
is bounded by the common first-level grid loss.
-/
theorem binaryEndpointAwareAdjacentRate_interior_ge_target_sub_first_log_of_bisection_bracket
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    {root lower delta target tFirst : ℝ}
    (hgHi : 0 ≤ sampleRate (adjacentHighIndex i))
    (hgLo : 0 ≤ sampleRate (adjacentLowIndex i))
    (hGpos :
      0 <
        sampleRate (adjacentHighIndex i) +
          sampleRate (adjacentLowIndex i))
    (hhi0 : 0 < successProb (adjacentHighIndex i))
    (hhi1 : successProb (adjacentHighIndex i) < 1)
    (hroot0 : 0 < root)
    (hreturned1 : successProb (adjacentLowIndex i) < 1)
    (htFirst0 : 0 < tFirst)
    (htFirst_le_root : tFirst ≤ root)
    (hdelta : 0 ≤ delta)
    (hroot_rate :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (successProb (adjacentHighIndex i)) root =
        target)
    (B :
      AppliedModelingLib.Optimization.RealBisectionBracket
        root lower (successProb (adjacentLowIndex i)) delta) :
    target -
        sampleRate (adjacentLowIndex i) *
          Real.log ((tFirst + delta) / tFirst) ≤
      binaryEndpointAwareAdjacentRate successProb sampleRate i := by
  have hlocal :
      target -
          sampleRate (adjacentLowIndex i) *
            Real.log ((root + delta) / root) ≤
        binaryEndpointAwareAdjacentRate successProb sampleRate i :=
    binaryEndpointAwareAdjacentRate_interior_ge_target_sub_low_shift_log_of_bisection_bracket
      successProb sampleRate i hfirst hlast hgHi hgLo hGpos hhi0 hhi1
      hroot0 hreturned1 hroot_rate B
  have hlog :
      Real.log ((root + delta) / root) ≤
        Real.log ((tFirst + delta) / tFirst) :=
    AppliedModelingLib.Math.log_add_div_self_le_log_add_div_self_of_le
      htFirst0 htFirst_le_root hdelta
  have hscaled :
      sampleRate (adjacentLowIndex i) *
          Real.log ((root + delta) / root) ≤
        sampleRate (adjacentLowIndex i) *
          Real.log ((tFirst + delta) / tFirst) :=
    mul_le_mul_of_nonneg_left hlog hgLo
  linarith

/-- Every adjacent endpoint-aware rate is positive on feasible endpoint levels. -/
theorem binaryEndpointAwareAdjacentRate_pos
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (i : Fin (m + 1)) :
    0 < binaryEndpointAwareAdjacentRate successProb sampleRate i := by
  by_cases hfirst : i.val = 0
  · let high : Fin (m + 2) := adjacentHighIndex i
    have hhigh_not_first : high.val ≠ 0 := by
      dsimp [high, adjacentHighIndex]
      omega
    have hhigh_not_last : high.val ≠ m + 1 := by
      dsimp [high, adjacentHighIndex]
      omega
    have hhigh_pos : 0 < successProb high :=
      BinaryEndpointLevelVector_pos_of_not_first hlevels high hhigh_not_first
    have hhigh_lt_one : successProb high < 1 :=
      BinaryEndpointLevelVector_lt_one_of_not_last hlevels high hhigh_not_last
    have hlog_neg : Real.log (1 - successProb high) < 0 :=
      Real.log_neg (sub_pos.mpr hhigh_lt_one) (by linarith)
    have hneglog_pos : 0 < -Real.log (1 - successProb high) := by
      linarith
    have hmul :
        0 <
          sampleRate high * (-Real.log (1 - successProb high)) :=
      mul_pos (by simpa [high] using hsample_high i) hneglog_pos
    simpa [binaryEndpointAwareAdjacentRate, hfirst, high] using hmul
  · by_cases hlast : i.val = m
    · let low : Fin (m + 2) := adjacentLowIndex i
      have hlow_not_first : low.val ≠ 0 := by
        dsimp [low, adjacentLowIndex]
        omega
      have hlow_not_last : low.val ≠ m + 1 := by
        dsimp [low, adjacentLowIndex]
        omega
      have hlow_pos : 0 < successProb low :=
        BinaryEndpointLevelVector_pos_of_not_first hlevels low hlow_not_first
      have hlow_lt_one : successProb low < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last hlevels low hlow_not_last
      have hlog_neg : Real.log (successProb low) < 0 :=
        Real.log_neg hlow_pos hlow_lt_one
      have hneglog_pos : 0 < -Real.log (successProb low) := by
        linarith
      have hmul :
          0 < sampleRate low * (-Real.log (successProb low)) :=
        mul_pos (by simpa [low] using hsample_low i) hneglog_pos
      simpa [binaryEndpointAwareAdjacentRate, hfirst, hlast, low,
        Nat.ne_of_gt hm] using hmul
    · have hlow_not_first : (adjacentLowIndex i).val ≠ 0 := by
        simpa [adjacentLowIndex] using hfirst
      have hhigh_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
        simp [adjacentHighIndex]
        omega
      have hpLo0 :
          0 < successProb (adjacentLowIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first
          hlevels (adjacentLowIndex i) hlow_not_first
      have hpHi1 :
          successProb (adjacentHighIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last
          hlevels (adjacentHighIndex i) hhigh_not_last
      have hpLo_lt_hi :
          successProb (adjacentLowIndex i) <
            successProb (adjacentHighIndex i) :=
        hlevels.2.2 i
      have hrate :
          0 <
            weightedBernoulliClosedThresholdRate
              (sampleRate (adjacentHighIndex i))
              (sampleRate (adjacentLowIndex i))
              (successProb (adjacentHighIndex i))
              (successProb (adjacentLowIndex i)) :=
        weightedBernoulliClosedThresholdRate_pos_of_lt
          (hsample_high i) (hsample_low i) hpLo0 hpLo_lt_hi hpHi1
      simpa [binaryEndpointAwareAdjacentRate, hfirst, hlast] using hrate

/--
First-endpoint monotonicity for Lemma 3.1's cascade: if the first adjacent
endpoint rate is raised above the candidate's equalized rate, then the first
interior level must move upward.
-/
theorem binaryEndpointAwareAdjacentRate_first_improvement_forces_high_increase
    {m : ℕ} (hm : 0 < m)
    (sampleRate candidate alternative : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halternative : BinaryEndpointLevelVector alternative)
    (hsample :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (heq_first :
      binaryEndpointAwareAdjacentRate candidate sampleRate
        (firstAdjacentIndex : Fin (m + 1)) = r)
    (hrate :
      r < binaryEndpointAwareAdjacentRate alternative sampleRate
        (firstAdjacentIndex : Fin (m + 1))) :
    candidate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) <
      alternative (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  let first : Fin (m + 1) := firstAdjacentIndex
  let high : Fin (m + 2) := adjacentHighIndex first
  have hc_lt_one :
      candidate high < 1 := by
    dsimp [high, first]
    exact BinaryEndpointLevelVector_first_high_lt_one hm hcandidate
  have ha_lt_one :
      alternative high < 1 := by
    dsimp [high, first]
    exact BinaryEndpointLevelVector_first_high_lt_one hm halternative
  have hrate_between :
      binaryEndpointAwareAdjacentRate candidate sampleRate first <
        binaryEndpointAwareAdjacentRate alternative sampleRate first := by
    have heq_first' :
        binaryEndpointAwareAdjacentRate candidate sampleRate first = r := by
      simpa [first] using heq_first
    have hrate' :
        r < binaryEndpointAwareAdjacentRate alternative sampleRate first := by
      simpa [first] using hrate
    simpa [heq_first'] using hrate'
  have hmul :
      sampleRate high * (-Real.log (1 - candidate high)) <
        sampleRate high * (-Real.log (1 - alternative high)) := by
    simpa [first, high, binaryEndpointAwareAdjacentRate,
      firstAdjacentIndex, adjacentHighIndex] using hrate_between
  have hneglog :
      -Real.log (1 - candidate high) <
        -Real.log (1 - alternative high) :=
    lt_of_mul_lt_mul_left hmul
      (le_of_lt (by simpa [high, first] using hsample))
  have hlog :
      Real.log (1 - alternative high) <
        Real.log (1 - candidate high) := by
    linarith
  have hsub :
      1 - alternative high < 1 - candidate high :=
    (Real.log_lt_log_iff
      (sub_pos.mpr ha_lt_one) (sub_pos.mpr hc_lt_one)).mp hlog
  dsimp [high, first] at hsub ⊢
  linarith

/--
First-endpoint strict monotonicity: increasing the first interior level
strictly increases the first adjacent endpoint-aware rate.
-/
theorem binaryEndpointAwareAdjacentRate_first_lt_of_high_lt
    {m : ℕ} (hm : 0 < m)
    (sampleRate candidate alternative : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halternative : BinaryEndpointLevelVector alternative)
    (hsample :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hhigh :
      candidate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) <
        alternative (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointAwareAdjacentRate candidate sampleRate
        (firstAdjacentIndex : Fin (m + 1)) <
      binaryEndpointAwareAdjacentRate alternative sampleRate
        (firstAdjacentIndex : Fin (m + 1)) := by
  let first : Fin (m + 1) := firstAdjacentIndex
  let high : Fin (m + 2) := adjacentHighIndex first
  have hc_lt_one : candidate high < 1 := by
    dsimp [high, first]
    exact BinaryEndpointLevelVector_first_high_lt_one hm hcandidate
  have ha_lt_one : alternative high < 1 := by
    dsimp [high, first]
    exact BinaryEndpointLevelVector_first_high_lt_one hm halternative
  have hhigh' : candidate high < alternative high := by
    simpa [high, first] using hhigh
  have hsub : 1 - alternative high < 1 - candidate high := by
    linarith
  have hlog :
      Real.log (1 - alternative high) <
        Real.log (1 - candidate high) :=
    Real.log_lt_log (sub_pos.mpr ha_lt_one) hsub
  have hneglog :
      -Real.log (1 - candidate high) <
        -Real.log (1 - alternative high) := by
    linarith
  have hmul :
      sampleRate high * (-Real.log (1 - candidate high)) <
        sampleRate high * (-Real.log (1 - alternative high)) :=
    mul_lt_mul_of_pos_left hneglog (by simpa [high, first] using hsample)
  simpa [first, high, binaryEndpointAwareAdjacentRate,
    firstAdjacentIndex, adjacentHighIndex] using hmul

/--
First-endpoint injectivity: equal first adjacent rates force the first
interior levels to agree.
-/
theorem binaryEndpointAwareAdjacentRate_first_high_eq_of_rate_eq
    {m : ℕ} (hm : 0 < m)
    (sampleRate candidate alternative : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halternative : BinaryEndpointLevelVector alternative)
    (hsample :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrate :
      binaryEndpointAwareAdjacentRate candidate sampleRate
          (firstAdjacentIndex : Fin (m + 1)) =
        binaryEndpointAwareAdjacentRate alternative sampleRate
          (firstAdjacentIndex : Fin (m + 1))) :
    candidate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) =
      alternative (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hrate_lt :=
      binaryEndpointAwareAdjacentRate_first_lt_of_high_lt
        hm sampleRate candidate alternative hcandidate halternative hsample hlt
    exact (not_lt_of_ge (le_of_eq hrate.symm)) hrate_lt
  · have hrate_lt :=
      binaryEndpointAwareAdjacentRate_first_lt_of_high_lt
        hm sampleRate alternative candidate halternative hcandidate hsample hgt
    exact (not_lt_of_ge (le_of_eq hrate)) hrate_lt

/--
Last-endpoint monotonicity for Lemma 3.1's cascade: if the previous cascade
step has moved the last interior level upward, then the last adjacent endpoint
rate cannot exceed the candidate's equalized rate.
-/
theorem binaryEndpointAwareAdjacentRate_last_increase_blocks_rate_improvement
    {m : ℕ} (hm : 0 < m)
    (sampleRate candidate alternative : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (heq_last :
      binaryEndpointAwareAdjacentRate candidate sampleRate
        (lastAdjacentIndex : Fin (m + 1)) = r)
    (hmove :
      candidate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
        alternative (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointAwareAdjacentRate alternative sampleRate
      (lastAdjacentIndex : Fin (m + 1)) ≤ r := by
  let last : Fin (m + 1) := lastAdjacentIndex
  let low : Fin (m + 2) := adjacentLowIndex last
  have hc_pos : 0 < candidate low := by
    dsimp [low, last]
    exact BinaryEndpointLevelVector_last_low_pos hm hcandidate
  have hlog :
      Real.log (candidate low) < Real.log (alternative low) :=
    Real.log_lt_log hc_pos (by simpa [low, last] using hmove)
  have hneglog :
      -Real.log (alternative low) < -Real.log (candidate low) := by
    linarith
  have hmul :
      sampleRate low * (-Real.log (alternative low)) <
        sampleRate low * (-Real.log (candidate low)) :=
    mul_lt_mul_of_pos_left hneglog
      (by simpa [low, last] using hsample)
  have hrate_between :
      binaryEndpointAwareAdjacentRate alternative sampleRate last <
        binaryEndpointAwareAdjacentRate candidate sampleRate last := by
    simpa [last, low, binaryEndpointAwareAdjacentRate,
      lastAdjacentIndex, adjacentLowIndex, Nat.ne_of_gt hm] using hmul
  have hrate_lt :
      binaryEndpointAwareAdjacentRate alternative sampleRate last < r := by
    simpa [last, heq_last] using hrate_between
  exact le_of_lt hrate_lt

/--
Last-endpoint strict monotonicity: increasing the last interior level strictly
decreases the last adjacent endpoint-aware rate.
-/
theorem binaryEndpointAwareAdjacentRate_last_lt_of_low_lt
    {m : ℕ} (hm : 0 < m)
    (sampleRate candidate alternative : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halternative : BinaryEndpointLevelVector alternative)
    (hsample :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hlow :
      candidate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
        alternative (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointAwareAdjacentRate alternative sampleRate
        (lastAdjacentIndex : Fin (m + 1)) <
      binaryEndpointAwareAdjacentRate candidate sampleRate
        (lastAdjacentIndex : Fin (m + 1)) := by
  let last : Fin (m + 1) := lastAdjacentIndex
  let low : Fin (m + 2) := adjacentLowIndex last
  have hc_pos : 0 < candidate low := by
    dsimp [low, last]
    exact BinaryEndpointLevelVector_last_low_pos hm hcandidate
  have hlog : Real.log (candidate low) < Real.log (alternative low) := by
    have hlow' : candidate low < alternative low := by
      simpa [low, last] using hlow
    exact Real.log_lt_log hc_pos hlow'
  have hneglog : -Real.log (alternative low) < -Real.log (candidate low) := by
    linarith
  have hmul :
      sampleRate low * (-Real.log (alternative low)) <
        sampleRate low * (-Real.log (candidate low)) :=
    mul_lt_mul_of_pos_left hneglog (by simpa [low, last] using hsample)
  have hm_ne : m ≠ 0 := Nat.ne_of_gt hm
  simpa [last, low, binaryEndpointAwareAdjacentRate,
    lastAdjacentIndex, adjacentLowIndex, hm_ne] using hmul

/-- Finite worst-adjacent endpoint-aware rate for a binary level chain. -/
def binaryEndpointAwareAdjacentRateObjective {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ) : ℝ :=
  AppliedModelingLib.finiteMin (binaryEndpointAwareAdjacentRate successProb sampleRate)

/-- Endpoint-aware adjacent rates equalize to one common value. -/
def BinaryEndpointAwareAdjacentRatesEqualize {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ) : Prop :=
  ∀ i j : Fin (m + 1),
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      binaryEndpointAwareAdjacentRate successProb sampleRate j

/--
In a uniform endpoint-aware equalized chain, the first high endpoint mirrors
the last low endpoint: `1 - t₁ = t_{M-2}`.  This is the endpoint form of the
equality between the first and last adjacent rates.
-/
theorem BinaryEndpointAwareAdjacentRatesEqualize_uniform_one_sub_first_high_eq_last_low
    {m : ℕ} (hm : 0 < m)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    1 - levels
          (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) =
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
  let first : Fin (m + 1) := firstAdjacentIndex
  let last : Fin (m + 1) := lastAdjacentIndex
  let firstHigh : Fin (m + 2) := adjacentHighIndex first
  let lastLow : Fin (m + 2) := adjacentLowIndex last
  have hfirstHigh_lt_one : levels firstHigh < 1 := by
    have hnot_last : firstHigh.val ≠ m + 1 := by
      simp [firstHigh, first]
      omega
    exact BinaryEndpointLevelVector_lt_one_of_not_last hlevels firstHigh hnot_last
  have hlastLow_pos : 0 < levels lastLow := by
    have hnot_first : lastLow.val ≠ 0 := by
      simp [lastLow, last]
      omega
    exact BinaryEndpointLevelVector_pos_of_not_first hlevels lastLow hnot_first
  have hcomp_pos : 0 < 1 - levels firstHigh := by
    linarith
  have hlast_formula :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) last =
        -Real.log (levels lastLow) := by
    have hfirst_last : last.val ≠ 0 := by
      simp [last]
      omega
    have hlast_last : last.val = m := by
      simp [last]
    simpa [lastLow] using
      binaryEndpointAwareAdjacentRate_last
        levels (fun _ : Fin (m + 2) => (1 : ℝ)) last
        hfirst_last hlast_last
  have hfirst_formula :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) first =
        -Real.log (1 - levels firstHigh) := by
    have hfirst_first : first.val = 0 := by
      simp [first]
    simpa [firstHigh] using
      binaryEndpointAwareAdjacentRate_first
        levels (fun _ : Fin (m + 2) => (1 : ℝ)) first
        hfirst_first
  have hneg_eq :
      -Real.log (1 - levels firstHigh) =
        -Real.log (levels lastLow) := by
    simpa [hfirst_formula, hlast_formula] using heq first last
  have hlog_eq :
      Real.log (1 - levels firstHigh) = Real.log (levels lastLow) := by
    linarith
  calc
    1 - levels firstHigh =
        Real.exp (Real.log (1 - levels firstHigh)) := by
          exact (Real.exp_log hcomp_pos).symm
    _ = Real.exp (Real.log (levels lastLow)) := by rw [hlog_eq]
    _ = levels lastLow := Real.exp_log hlastLow_pos

/--
Endpoint-mirror bridge used by Theorem 3.2: if a returned vector is at least
the equalized optimal vector at the first high endpoint and the last low
endpoint, then it satisfies the mirror inequality that implies
`r(last) ≤ r(first)`.
-/
theorem BinaryEndpointAwareAdjacentRatesEqualize_uniform_endpoint_mirror_of_endpoint_ge
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    (hoptimalLevels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hfirst_ge :
      optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤
        returned (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hlast_ge :
      optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
        returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :
    1 -
        returned (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤
      returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
  have hmirror_opt :=
    BinaryEndpointAwareAdjacentRatesEqualize_uniform_one_sub_first_high_eq_last_low
      hm optimal hoptimalLevels heq
  calc
    1 -
        returned (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤
        1 -
          optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
          linarith
    _ =
        optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := hmirror_opt
    _ ≤ returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := hlast_ge

/--
Uniformly spaced endpoint levels on `[0,1]`.  This is the concrete feasible
chain used for coarse lower bounds on the optimal uniform finite objective.
-/
def uniformEndpointLevels (m : ℕ) : Fin (m + 2) → ℝ :=
  fun i => (i.1 : ℝ) / ((m + 1 : ℕ) : ℝ)

/-- Uniform endpoint levels satisfy the paper's endpoint convention. -/
theorem uniformEndpointLevels_isEndpointLevelVector (m : ℕ) :
    BinaryEndpointLevelVector (uniformEndpointLevels m) := by
  constructor
  · simp [uniformEndpointLevels]
  constructor
  · have hden : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hdiv : ((m : ℝ) + 1) / ((m : ℝ) + 1) = 1 := by
      field_simp [hden]
    simpa [uniformEndpointLevels, lastLevelIndex] using hdiv
  · intro i
    have hden_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    simp [uniformEndpointLevels, adjacentLowIndex, adjacentHighIndex]
    exact div_lt_div_of_pos_right (by norm_num) hden_pos

/-- Every adjacent width in the uniform endpoint vector is `1 / (m+1)`. -/
theorem uniformEndpointLevels_adjacent_width (m : ℕ) (i : Fin (m + 1)) :
    uniformEndpointLevels m (adjacentHighIndex i) -
        uniformEndpointLevels m (adjacentLowIndex i) =
      1 / ((m + 1 : ℕ) : ℝ) := by
  have hden : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp [uniformEndpointLevels, adjacentLowIndex, adjacentHighIndex]
  field_simp [hden]
  ring

/--
Uniform-matching fixed-width upper bound for each endpoint-aware adjacent
rate: with sample rates all equal to one, an adjacent interval of width `x`
has rate at most the last-endpoint rate with the same width, `-log (1 - x)`.
-/
theorem binaryEndpointAwareAdjacentRate_uniform_le_neg_log_one_sub_width
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ} (hlevels : BinaryEndpointLevelVector levels)
    (i : Fin (m + 1)) :
    binaryEndpointAwareAdjacentRate levels (fun _ : Fin (m + 2) => (1 : ℝ)) i ≤
      -Real.log
        (1 - (levels (adjacentHighIndex i) - levels (adjacentLowIndex i))) := by
  by_cases hfirst : i.val = 0
  · have hlow_zero :
        levels (adjacentLowIndex i) = 0 := by
      have hi : adjacentLowIndex i = (firstLevelIndex : Fin (m + 2)) := by
        ext
        simpa [adjacentLowIndex, firstLevelIndex] using hfirst
      simpa [hi] using hlevels.1
    have hrate :=
      binaryEndpointAwareAdjacentRate_first
        levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hfirst
    rw [hrate, hlow_zero]
    ring_nf
    exact le_rfl
  · by_cases hlast : i.val = m
    · have hlast_high :
          levels (adjacentHighIndex i) = 1 := by
        have hi : adjacentHighIndex i = (lastLevelIndex : Fin (m + 2)) := by
          ext
          simpa [adjacentHighIndex, lastLevelIndex] using hlast
        simpa [hi] using hlevels.2.1
      have hrate :=
        binaryEndpointAwareAdjacentRate_last
          levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hfirst hlast
      rw [hrate, hlast_high]
      ring_nf
      exact le_rfl
    · let pLo : ℝ := levels (adjacentLowIndex i)
      let x : ℝ := levels (adjacentHighIndex i) - levels (adjacentLowIndex i)
      have hpLo0 : 0 ≤ pLo := by
        dsimp [pLo]
        exact BinaryEndpointLevelVector_nonneg hlevels (adjacentLowIndex i)
      have hx0 : 0 ≤ x := by
        dsimp [x]
        exact sub_nonneg.mpr (BinaryEndpointLevelVector_adjacent_ordered hlevels i)
      have hhi1 : pLo + x ≤ 1 := by
        dsimp [pLo, x]
        have hhigh_le :=
          BinaryEndpointLevelVector_le_one hlevels (adjacentHighIndex i)
        linarith
      have hpLo_pos : 0 < pLo := by
        dsimp [pLo]
        have hlow_not_first : (adjacentLowIndex i).val ≠ 0 := by
          simpa [adjacentLowIndex] using hfirst
        exact
          BinaryEndpointLevelVector_pos_of_not_first
            hlevels (adjacentLowIndex i) hlow_not_first
      have hx1 : x < 1 := by
        dsimp [x, pLo] at hpLo_pos
        have hhigh_le :=
          BinaryEndpointLevelVector_le_one hlevels (adjacentHighIndex i)
        linarith
      have hlib :
          weightedBernoulliClosedThresholdRate 1 1 (pLo + x) pLo ≤
            -Real.log (1 - x) :=
        weightedBernoulliClosedThresholdRate_one_one_le_neg_log_one_sub_width
          hpLo0 hx0 hhi1 hx1
      have hrate :=
        binaryEndpointAwareAdjacentRate_interior
          levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hfirst hlast
      have hpHi_eq :
          levels (adjacentHighIndex i) = pLo + x := by
        dsimp [pLo, x]
        ring
      rw [hrate, hpHi_eq]
      simpa [pLo, x] using hlib

/-- Uniform-matching last adjacent rate, written as a function of last width. -/
theorem binaryEndpointAwareAdjacentRate_uniform_last_eq_neg_log_one_sub_width
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ} (hlevels : BinaryEndpointLevelVector levels) :
    binaryEndpointAwareAdjacentRate levels (fun _ : Fin (m + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin (m + 1)) =
      -Real.log
        (1 -
          (levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))) := by
  have hrate :=
    binaryEndpointAwareAdjacentRate_last
      levels (fun _ : Fin (m + 2) => (1 : ℝ))
      (lastAdjacentIndex : Fin (m + 1))
      (by simp [Nat.ne_of_gt hm])
      (by simp)
  have hlast_high :
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) = 1 := by
    simpa [lastAdjacentIndex, adjacentHighIndex, lastLevelIndex] using
      hlevels.2.1
  rw [hrate, hlast_high]
  ring_nf

/--
Uniform-matching gap separation for one adjacent interval: every endpoint-aware
adjacent rate is at least the elementary lower bound
`-log (1 - width^2)` for that adjacent probability width.
-/
theorem binaryEndpointAwareAdjacentRate_uniform_ge_neg_log_one_sub_width_sq
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ} (hlevels : BinaryEndpointLevelVector levels)
    (i : Fin (m + 1)) :
    -Real.log
        (1 -
          (levels (adjacentHighIndex i) - levels (adjacentLowIndex i)) ^ 2) ≤
      binaryEndpointAwareAdjacentRate levels
        (fun _ : Fin (m + 2) => (1 : ℝ)) i := by
  by_cases hfirst : i.val = 0
  · have hlow_zero :
        levels (adjacentLowIndex i) = 0 := by
      have hi : adjacentLowIndex i = (firstLevelIndex : Fin (m + 2)) := by
        ext
        simpa [adjacentLowIndex, firstLevelIndex] using hfirst
      simpa [hi] using hlevels.1
    have hhigh_nonneg :
        0 ≤ levels (adjacentHighIndex i) := by
      exact BinaryEndpointLevelVector_nonneg hlevels (adjacentHighIndex i)
    have hhigh_lt_one :
        levels (adjacentHighIndex i) < 1 := by
      have hnot_last : (adjacentHighIndex i).val ≠ m + 1 := by
        simp [adjacentHighIndex]
        omega
      exact
        BinaryEndpointLevelVector_lt_one_of_not_last
          hlevels (adjacentHighIndex i) hnot_last
    have hlog :=
      AppliedModelingLib.Math.neg_log_one_sub_sq_le_neg_log_one_sub
        hhigh_nonneg hhigh_lt_one
    have hrate :=
      binaryEndpointAwareAdjacentRate_first
        levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hfirst
    simpa [hrate, hlow_zero] using hlog
  · by_cases hlast : i.val = m
    · have hhigh_one :
          levels (adjacentHighIndex i) = 1 := by
        have hi : adjacentHighIndex i = (lastLevelIndex : Fin (m + 2)) := by
          ext
          simpa [adjacentHighIndex, lastLevelIndex] using hlast
        simpa [hi] using hlevels.2.1
      have hlow_pos :
          0 < levels (adjacentLowIndex i) := by
        have hnot_first : (adjacentLowIndex i).val ≠ 0 := by
          simpa [adjacentLowIndex] using hfirst
        exact
          BinaryEndpointLevelVector_pos_of_not_first
            hlevels (adjacentLowIndex i) hnot_first
      have hwidth_nonneg :
          0 ≤ 1 - levels (adjacentLowIndex i) := by
        have hlow_le_one :=
          BinaryEndpointLevelVector_le_one hlevels (adjacentLowIndex i)
        linarith
      have hwidth_lt_one :
          1 - levels (adjacentLowIndex i) < 1 := by
        linarith
      have hlog :=
        AppliedModelingLib.Math.neg_log_one_sub_sq_le_neg_log_one_sub
          hwidth_nonneg hwidth_lt_one
      have hrate :=
        binaryEndpointAwareAdjacentRate_last
          levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hfirst hlast
      simpa [hrate, hhigh_one] using hlog
    · let pLo : ℝ := levels (adjacentLowIndex i)
      let x : ℝ := levels (adjacentHighIndex i) - levels (adjacentLowIndex i)
      have hpLo0 : 0 ≤ pLo := by
        dsimp [pLo]
        exact BinaryEndpointLevelVector_nonneg hlevels (adjacentLowIndex i)
      have hx0 : 0 ≤ x := by
        dsimp [x]
        exact sub_nonneg.mpr (BinaryEndpointLevelVector_adjacent_ordered hlevels i)
      have hhi_eq : pLo + x = levels (adjacentHighIndex i) := by
        dsimp [pLo, x]
        ring
      have hhi1 : pLo + x ≤ 1 := by
        rw [hhi_eq]
        exact BinaryEndpointLevelVector_le_one hlevels (adjacentHighIndex i)
      have hx1 : x < 1 := by
        dsimp [x, pLo]
        have hlow_pos : 0 < levels (adjacentLowIndex i) := by
          have hnot_first : (adjacentLowIndex i).val ≠ 0 := by
            simpa [adjacentLowIndex] using hfirst
          exact
            BinaryEndpointLevelVector_pos_of_not_first
              hlevels (adjacentLowIndex i) hnot_first
        have hhigh_le_one :=
          BinaryEndpointLevelVector_le_one hlevels (adjacentHighIndex i)
        linarith
      have hlib :
          -Real.log (1 - x ^ 2) ≤
            weightedBernoulliClosedThresholdRate 1 1 (pLo + x) pLo :=
        weightedBernoulliClosedThresholdRate_one_one_ge_neg_log_one_sub_width_sq
          hpLo0 hx0 hhi1 hx1
      have hrate :=
        binaryEndpointAwareAdjacentRate_interior
          levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hfirst hlast
      simpa [pLo, x, hhi_eq, hrate] using hlib

/-- Adjacent endpoint-vector widths are nonnegative. -/
theorem BinaryEndpointLevelVector_adjacent_width_nonneg
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (i : Fin (m + 1)) :
    0 ≤ levels (adjacentHighIndex i) - levels (adjacentLowIndex i) :=
  sub_nonneg.mpr (BinaryEndpointLevelVector_adjacent_ordered hlevels i)

/--
If there is at least one interior level, each adjacent endpoint-vector width is
strictly below one.
-/
theorem BinaryEndpointLevelVector_adjacent_width_lt_one
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (i : Fin (m + 1)) :
    levels (adjacentHighIndex i) - levels (adjacentLowIndex i) < 1 := by
  by_cases hlast : i.val = m
  · have hhigh_one :
        levels (adjacentHighIndex i) = 1 := by
      have hi : adjacentHighIndex i = (lastLevelIndex : Fin (m + 2)) := by
        ext
        simpa [adjacentHighIndex, lastLevelIndex] using hlast
      simpa [hi] using hlevels.2.1
    have hlow_pos : 0 < levels (adjacentLowIndex i) := by
      have hlow_not_first : (adjacentLowIndex i).val ≠ 0 := by
        have hlow_val : (adjacentLowIndex i).val = m := by
          simpa [adjacentLowIndex] using hlast
        intro hzero
        have hm0 : m = 0 := by omega
        exact (Nat.ne_of_gt hm) hm0
      exact
        BinaryEndpointLevelVector_pos_of_not_first
          hlevels (adjacentLowIndex i) hlow_not_first
    linarith
  · have hhigh_lt_one :
        levels (adjacentHighIndex i) < 1 := by
      have hhigh_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
        simp [adjacentHighIndex]
        omega
      exact
        BinaryEndpointLevelVector_lt_one_of_not_last
          hlevels (adjacentHighIndex i) hhigh_not_last
    have hlow_nonneg :
        0 ≤ levels (adjacentLowIndex i) :=
      BinaryEndpointLevelVector_nonneg hlevels (adjacentLowIndex i)
    linarith

/--
Uniform-matching gap separation: an adjacent interval of width at least
`ε > 0` forces the corresponding endpoint-aware rate to be bounded below by
the positive elementary rate `-log (1 - ε^2)`.
-/
theorem binaryEndpointAwareAdjacentRate_uniform_gap_ge_neg_log_one_sub_sq
    {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (i : Fin (m + 1))
    (hgap :
      ε ≤ levels (adjacentHighIndex i) - levels (adjacentLowIndex i)) :
    -Real.log (1 - ε ^ 2) ≤
      binaryEndpointAwareAdjacentRate levels
        (fun _ : Fin (m + 2) => (1 : ℝ)) i := by
  have hwidth_lt :
      levels (adjacentHighIndex i) - levels (adjacentLowIndex i) < 1 :=
    BinaryEndpointLevelVector_adjacent_width_lt_one hm hlevels i
  have hmono :
      -Real.log (1 - ε ^ 2) ≤
        -Real.log
          (1 -
            (levels (adjacentHighIndex i) -
              levels (adjacentLowIndex i)) ^ 2) :=
    AppliedModelingLib.Math.neg_log_one_sub_sq_mono hε.le hgap hwidth_lt
  exact
    hmono.trans
      (binaryEndpointAwareAdjacentRate_uniform_ge_neg_log_one_sub_width_sq
        hm hlevels i)

/--
The uniformly spaced endpoint vector gives a concrete polynomial lower bound
on the uniform finite adjacent-rate objective.
-/
theorem uniformEndpointLevels_objective_ge_inv_adjacent_count_sq
    {m : ℕ} (hm : 0 < m) :
    (1 / ((m + 1 : ℕ) : ℝ)) ^ 2 ≤
      binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  let ε : ℝ := 1 / ((m + 1 : ℕ) : ℝ)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact one_div_pos.mpr (by exact_mod_cast (Nat.succ_pos m))
  have hε_lt_one : ε < 1 := by
    dsimp [ε]
    have hone_lt : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ m + 1)
    have h :=
      one_div_lt_one_div_of_lt (a := (1 : ℝ))
        (b := ((m + 1 : ℕ) : ℝ)) zero_lt_one hone_lt
    simpa using h
  have hε_sq_lt_one : ε ^ 2 < 1 := by
    exact (sq_lt_one_iff₀ hε_pos.le).mpr hε_lt_one
  have hlog_lower : ε ^ 2 ≤ -Real.log (1 - ε ^ 2) :=
    AppliedModelingLib.Math.le_neg_log_one_sub (sq_nonneg ε) hε_sq_lt_one
  have hpoint :
      ∀ i : Fin (m + 1),
        -Real.log (1 - ε ^ 2) ≤
          binaryEndpointAwareAdjacentRate (uniformEndpointLevels m)
            (fun _ : Fin (m + 2) => (1 : ℝ)) i := by
    intro i
    refine
      binaryEndpointAwareAdjacentRate_uniform_gap_ge_neg_log_one_sub_sq
        hε_pos hm (uniformEndpointLevels_isEndpointLevelVector m) i ?_
    dsimp [ε]
    rw [uniformEndpointLevels_adjacent_width]
  calc
    (1 / ((m + 1 : ℕ) : ℝ)) ^ 2 = ε ^ 2 := by rfl
    _ ≤ -Real.log (1 - ε ^ 2) := hlog_lower
    _ ≤
        binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m)
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
        unfold binaryEndpointAwareAdjacentRateObjective
        exact AppliedModelingLib.le_finiteMin
          (binaryEndpointAwareAdjacentRate (uniformEndpointLevels m)
            (fun _ : Fin (m + 2) => (1 : ℝ))) hpoint

/--
For monotone sample rates normalized so that the first nonzero type has rate
one, every adjacent rate of the uniformly spaced endpoint vector is at least
its uniform-sampling counterpart.  This is the finite comparison used in the
source proof of Corollary C.3 after scaling `g_1 = 1`.
-/
theorem binaryEndpointAwareAdjacentRate_uniformEndpointLevels_le_of_sampleRate_mono_first_eq_one
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (i : Fin (m + 1)) :
    binaryEndpointAwareAdjacentRate (uniformEndpointLevels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)) i ≤
      binaryEndpointAwareAdjacentRate (uniformEndpointLevels m) sampleRate i := by
  let levels : Fin (m + 2) → ℝ := uniformEndpointLevels m
  let first : Fin (m + 1) := firstAdjacentIndex
  let firstHigh : Fin (m + 2) := adjacentHighIndex first
  have hfirst_sample' : sampleRate firstHigh = 1 := by
    simpa [firstHigh, first] using hfirst_sample
  have hfirstHigh_val : firstHigh.val = 1 := by
    simp [firstHigh, first]
  have hlevels : BinaryEndpointLevelVector levels :=
    uniformEndpointLevels_isEndpointLevelVector m
  by_cases hi_first : i.val = 0
  · have hi_eq_first : i = first := by
      ext
      simpa [first, firstAdjacentIndex] using hi_first
    subst i
    have hrate_uniform :
        binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ)) first =
          (1 : ℝ) *
            (-Real.log (1 - levels firstHigh)) := by
      simpa [levels, first, firstHigh] using
        binaryEndpointAwareAdjacentRate_first
          levels (fun _ : Fin (m + 2) => (1 : ℝ)) first (by simp [first])
    have hrate_sample :
        binaryEndpointAwareAdjacentRate levels sampleRate first =
          sampleRate firstHigh *
            (-Real.log (1 - levels firstHigh)) := by
      simpa [levels, first, firstHigh] using
        binaryEndpointAwareAdjacentRate_first
          levels sampleRate first (by simp [first])
    rw [hrate_uniform, hrate_sample, hfirst_sample']
  · by_cases hi_last : i.val = m
    · let low : Fin (m + 2) := adjacentLowIndex i
      have hrate_uniform :
          binaryEndpointAwareAdjacentRate levels
              (fun _ : Fin (m + 2) => (1 : ℝ)) i =
            (1 : ℝ) * (-Real.log (levels low)) := by
        simpa [levels, low] using
          binaryEndpointAwareAdjacentRate_last
            levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hi_first hi_last
      have hrate_sample :
          binaryEndpointAwareAdjacentRate levels sampleRate i =
            sampleRate low * (-Real.log (levels low)) := by
        simpa [levels, low] using
          binaryEndpointAwareAdjacentRate_last
            levels sampleRate i hi_first hi_last
      have hfirst_le_low : firstHigh.val ≤ low.val := by
        have hlow_val : low.val = i.val := by
          simp [low, adjacentLowIndex]
        rw [hfirstHigh_val, hlow_val, hi_last]
        omega
      have hsample_low_ge_one : 1 ≤ sampleRate low := by
        calc
          (1 : ℝ) = sampleRate firstHigh := hfirst_sample'.symm
          _ ≤ sampleRate low := hsample_mono hfirst_le_low
      have hlow_pos : 0 < levels low := by
        have hlow_val : low.val = i.val := by
          simp [low, adjacentLowIndex]
        exact BinaryEndpointLevelVector_pos_of_not_first hlevels low (by
          rw [hlow_val, hi_last]
          omega)
      have hlow_le_one : levels low ≤ 1 :=
        BinaryEndpointLevelVector_le_one hlevels low
      have hlog_nonneg : 0 ≤ -Real.log (levels low) := by
        have hlog_le : Real.log (levels low) ≤ Real.log (1 : ℝ) :=
          Real.log_le_log hlow_pos hlow_le_one
        linarith [Real.log_one]
      rw [hrate_uniform, hrate_sample]
      simpa using mul_le_mul_of_nonneg_right hsample_low_ge_one hlog_nonneg
    · have hrate_uniform :
          binaryEndpointAwareAdjacentRate levels
              (fun _ : Fin (m + 2) => (1 : ℝ)) i =
            weightedBernoulliClosedThresholdRate
              (1 : ℝ) (1 : ℝ)
              (levels (adjacentHighIndex i))
              (levels (adjacentLowIndex i)) := by
        simpa [levels] using
          binaryEndpointAwareAdjacentRate_interior
            levels (fun _ : Fin (m + 2) => (1 : ℝ)) i hi_first hi_last
      have hrate_sample :
          binaryEndpointAwareAdjacentRate levels sampleRate i =
            weightedBernoulliClosedThresholdRate
              (sampleRate (adjacentHighIndex i))
              (sampleRate (adjacentLowIndex i))
              (levels (adjacentHighIndex i))
              (levels (adjacentLowIndex i)) := by
        simpa [levels] using
          binaryEndpointAwareAdjacentRate_interior
            levels sampleRate i hi_first hi_last
      have hfirst_le_low :
          firstHigh.val ≤ (adjacentLowIndex i).val := by
        have hlow_val : (adjacentLowIndex i).val = i.val := by
          simp [adjacentLowIndex]
        rw [hfirstHigh_val, hlow_val]
        omega
      have hfirst_le_high :
          firstHigh.val ≤ (adjacentHighIndex i).val := by
        simp [hfirstHigh_val, adjacentHighIndex]
      have hsample_low_ge_one :
          (1 : ℝ) ≤ sampleRate (adjacentLowIndex i) := by
        calc
          (1 : ℝ) = sampleRate firstHigh := hfirst_sample'.symm
          _ ≤ sampleRate (adjacentLowIndex i) := hsample_mono hfirst_le_low
      have hsample_high_ge_one :
          (1 : ℝ) ≤ sampleRate (adjacentHighIndex i) := by
        calc
          (1 : ℝ) = sampleRate firstHigh := hfirst_sample'.symm
          _ ≤ sampleRate (adjacentHighIndex i) := hsample_mono hfirst_le_high
      have hpHi0 : 0 < levels (adjacentHighIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first hlevels
          (adjacentHighIndex i) (by
            have hhigh_val : (adjacentHighIndex i).val = i.val + 1 := by
              simp [adjacentHighIndex]
            rw [hhigh_val]
            omega)
      have hpHi1 : levels (adjacentHighIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last hlevels
          (adjacentHighIndex i) (by
            have hhigh_val : (adjacentHighIndex i).val = i.val + 1 := by
              simp [adjacentHighIndex]
            rw [hhigh_val]
            omega)
      have hpLo0 : 0 < levels (adjacentLowIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first hlevels
          (adjacentLowIndex i) (by
            have hlow_val : (adjacentLowIndex i).val = i.val := by
              simp [adjacentLowIndex]
            rw [hlow_val]
            omega)
      have hpLo1 : levels (adjacentLowIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last hlevels
          (adjacentLowIndex i) (by
            have hlow_val : (adjacentLowIndex i).val = i.val := by
              simp [adjacentLowIndex]
            rw [hlow_val]
            omega)
      rw [hrate_uniform, hrate_sample]
      exact
        weightedBernoulliClosedThresholdRate_le_of_weights_le
          (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
          (hsample_pos (adjacentHighIndex i))
          (hsample_pos (adjacentLowIndex i))
          hsample_high_ge_one hsample_low_ge_one
          hpHi0 hpHi1 hpLo0 hpLo1

/--
Scaling both sample weights by the same positive constant scales the closed
Bernoulli threshold exponent by that constant.  The normalized powers in the
closed-rate base are unchanged.
-/
theorem weightedBernoulliClosedThresholdRate_same_weights_eq_mul_uniform
    {g pHi pLo : ℝ} (hg : 0 < g) :
    weightedBernoulliClosedThresholdRate g g pHi pLo =
      g * weightedBernoulliClosedThresholdRate 1 1 pHi pLo := by
  have hratio : g / (g + g) = (1 : ℝ) / 2 := by
    have hden : g + g ≠ 0 := by nlinarith
    apply (div_eq_iff hden).2
    ring
  simp only [weightedBernoulliClosedThresholdRate,
    weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
    weightedBernoulliSuccessBase]
  rw [hratio]
  norm_num
  ring

/--
If a positive sample-rate vector is nondecreasing, each adjacent exponent is
at most the exponent obtained by replacing both local sample rates by the
last interior sample rate.  This is the weight-comparison step used in the
source proof of Lemma C.6.
-/
theorem binaryEndpointAwareAdjacentRate_le_last_sample_uniformized_of_mono
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (i : Fin (m + 1)) :
    binaryEndpointAwareAdjacentRate levels sampleRate i ≤
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i := by
  let lastLow : Fin (m + 2) :=
    adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))
  let gLast : ℝ := sampleRate lastLow
  have hgLast : 0 < gLast := hsample_pos lastLow
  by_cases hfirst : i.val = 0
  · have hlocal_le : sampleRate (adjacentHighIndex i) ≤ gLast := by
      apply hsample_mono
      simp [lastLow, adjacentHighIndex]
      omega
    have hlog_nonneg :
        0 ≤ -Real.log (1 - levels (adjacentHighIndex i)) := by
      have hhigh_pos : 0 < levels (adjacentHighIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first hlevels
          (adjacentHighIndex i) (by simp [adjacentHighIndex])
      have hhigh_le_one : levels (adjacentHighIndex i) ≤ 1 :=
        BinaryEndpointLevelVector_le_one hlevels (adjacentHighIndex i)
      have hone_sub_mem : 1 - levels (adjacentHighIndex i) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith
      exact neg_nonneg.mpr
        (Real.log_nonpos hone_sub_mem.1 hone_sub_mem.2)
    rw [binaryEndpointAwareAdjacentRate_first levels sampleRate i hfirst,
      binaryEndpointAwareAdjacentRate_first levels
        (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i hfirst]
    simpa [gLast] using mul_le_mul_of_nonneg_right hlocal_le hlog_nonneg
  · by_cases hlast : i.val = m
    · have hi : adjacentLowIndex i = lastLow := by
        ext
        simp [lastLow, adjacentLowIndex, hlast]
      have hi_sample :
          sampleRate (adjacentLowIndex i) = sampleRate lastLow :=
        congrArg sampleRate hi
      rw [binaryEndpointAwareAdjacentRate_last levels sampleRate i hfirst hlast,
        binaryEndpointAwareAdjacentRate_last levels
          (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i hfirst hlast, hi_sample]
      simp [lastLow]
    · have hlow_le : sampleRate (adjacentLowIndex i) ≤ gLast := by
        apply hsample_mono
        simp [lastLow, adjacentLowIndex]
        omega
      have hhigh_le : sampleRate (adjacentHighIndex i) ≤ gLast := by
        apply hsample_mono
        simp [lastLow, adjacentHighIndex]
        omega
      have hpHi0 : 0 < levels (adjacentHighIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first hlevels
          (adjacentHighIndex i) (by simp [adjacentHighIndex])
      have hpHi1 : levels (adjacentHighIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last hlevels
          (adjacentHighIndex i) (by
            simp [adjacentHighIndex]
            omega)
      have hpLo0 : 0 < levels (adjacentLowIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first hlevels
          (adjacentLowIndex i) (by
            simpa [adjacentLowIndex] using hfirst)
      have hpLo1 : levels (adjacentLowIndex i) < 1 :=
        lt_of_le_of_lt
          (BinaryEndpointLevelVector_adjacent_ordered hlevels i) hpHi1
      rw [binaryEndpointAwareAdjacentRate_interior levels sampleRate i hfirst hlast,
        binaryEndpointAwareAdjacentRate_interior levels
          (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i hfirst hlast]
      calc
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (levels (adjacentHighIndex i)) (levels (adjacentLowIndex i))
            ≤ weightedBernoulliClosedThresholdRate gLast gLast
                (levels (adjacentHighIndex i)) (levels (adjacentLowIndex i)) :=
          weightedBernoulliClosedThresholdRate_le_of_weights_le
            (hsample_pos (adjacentHighIndex i))
            (hsample_pos (adjacentLowIndex i)) hgLast hgLast
            hhigh_le hlow_le hpHi0 hpHi1 hpLo0 hpLo1
        _ = gLast * weightedBernoulliClosedThresholdRate 1 1
              (levels (adjacentHighIndex i)) (levels (adjacentLowIndex i)) :=
          weightedBernoulliClosedThresholdRate_same_weights_eq_mul_uniform hgLast

/--
Lemma C.6 rate-comparison bridge: if every interval narrower than the last
one would have strictly smaller adjacent rate than the last interval, then
equalized adjacent rates force the last interval to be no wider than every
interval.
-/
theorem BinaryEndpointAwareAdjacentRatesEqualize_last_width_le_all_of_rate_strict_of_width_lt
    {m : ℕ} {levels sampleRate : Fin (m + 2) → ℝ}
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hrate_strict :
      ∀ i : Fin (m + 1),
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) <
            levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
              levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) →
          binaryEndpointAwareAdjacentRate levels sampleRate i <
            binaryEndpointAwareAdjacentRate levels sampleRate
              (lastAdjacentIndex : Fin (m + 1))) :
    ∀ i : Fin (m + 1),
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) := by
  intro i
  by_contra hnot
  have hlt :
      levels (adjacentHighIndex i) - levels (adjacentLowIndex i) <
        levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
    lt_of_not_ge hnot
  have hrate_lt := hrate_strict i hlt
  have hrate_eq :
      binaryEndpointAwareAdjacentRate levels sampleRate i =
        binaryEndpointAwareAdjacentRate levels sampleRate
          (lastAdjacentIndex : Fin (m + 1)) :=
    heq i (lastAdjacentIndex : Fin (m + 1))
  exact (not_lt_of_ge (le_of_eq hrate_eq.symm)) hrate_lt

/--
General monotone-matching Lemma C.6 width comparison.  If adjacent rates are
equalized and sample rates are positive and nondecreasing, the last interval
is no wider than any other interval.
-/
theorem BinaryEndpointAwareAdjacentRatesEqualize_monotone_last_width_le_all
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b) :
    ∀ i : Fin (m + 1),
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) := by
  apply
    BinaryEndpointAwareAdjacentRatesEqualize_last_width_le_all_of_rate_strict_of_width_lt
      heq
  intro i hwidth_lt
  let wi : ℝ :=
    levels (adjacentHighIndex i) - levels (adjacentLowIndex i)
  let wl : ℝ :=
    levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  let lastLow : Fin (m + 2) :=
    adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))
  let gLast : ℝ := sampleRate lastLow
  have hgLast : 0 < gLast := hsample_pos lastLow
  have hwi_uniform :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i ≤
        -Real.log (1 - wi) := by
    simpa [wi] using
      binaryEndpointAwareAdjacentRate_uniform_le_neg_log_one_sub_width
        hm hlevels i
  have hactual_le :
      binaryEndpointAwareAdjacentRate levels sampleRate i ≤
        gLast * binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i := by
    simpa [gLast, lastLow] using
      binaryEndpointAwareAdjacentRate_le_last_sample_uniformized_of_mono
        hm hlevels hsample_pos hsample_mono i
  have hwl_lt_one : wl < 1 := by
    dsimp [wl]
    exact
      BinaryEndpointLevelVector_adjacent_width_lt_one hm hlevels
        (lastAdjacentIndex : Fin (m + 1))
  have hwi_lt_wl : wi < wl := by simpa [wi, wl] using hwidth_lt
  have hlog_lt : -Real.log (1 - wi) < -Real.log (1 - wl) := by
    have hone_sub_wl_pos : 0 < 1 - wl := by linarith
    have hone_sub_lt : 1 - wl < 1 - wi := by linarith
    have := Real.log_lt_log hone_sub_wl_pos hone_sub_lt
    linarith
  have hlast_rate :
      binaryEndpointAwareAdjacentRate levels sampleRate
          (lastAdjacentIndex : Fin (m + 1)) =
        gLast * (-Real.log (1 - wl)) := by
    have hlast :=
      binaryEndpointAwareAdjacentRate_last levels sampleRate
        (lastAdjacentIndex : Fin (m + 1)) (by
          simp
          omega) (by simp)
    have hlast_high :
        levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) = 1 := by
      simpa [lastAdjacentIndex, adjacentHighIndex, lastLevelIndex] using
        hlevels.2.1
    have hone_sub_wl :
        1 - wl =
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
      dsimp [wl]
      have hlast_high' :
          levels ((⟨m + 1, by omega⟩ : Fin (m + 2))) = 1 := by
        simpa [lastAdjacentIndex, adjacentHighIndex] using hlast_high
      rw [hlast_high']
      ring
    simpa [gLast, lastLow, hone_sub_wl] using hlast
  calc
    binaryEndpointAwareAdjacentRate levels sampleRate i
        ≤ gLast * binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) ↦ (1 : ℝ)) i := hactual_le
    _ ≤ gLast * (-Real.log (1 - wi)) :=
      mul_le_mul_of_nonneg_left hwi_uniform hgLast.le
    _ < gLast * (-Real.log (1 - wl)) :=
      mul_lt_mul_of_pos_left hlog_lt hgLast
    _ = binaryEndpointAwareAdjacentRate levels sampleRate
          (lastAdjacentIndex : Fin (m + 1)) := hlast_rate.symm

/--
Lemma C.6 as stated for a general positive nondecreasing matching function:
the penultimate level is at least `1 - 1/(m+1)`.
-/
theorem BinaryEndpointLevelVector_monotone_equalized_last_low_ge_one_sub_inv
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_last_width_le_all
    hlevels
    (BinaryEndpointAwareAdjacentRatesEqualize_monotone_last_width_le_all
      hm hlevels heq hsample_pos hsample_mono)

/--
Uniform-matching Lemma C.6 width-minimality: for endpoint-normalized levels
with all adjacent rates equal under uniform sample rates, the last adjacent
interval is no wider than every adjacent interval.
-/
theorem BinaryEndpointAwareAdjacentRatesEqualize_uniform_last_width_le_all
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∀ i : Fin (m + 1),
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) := by
  apply
    BinaryEndpointAwareAdjacentRatesEqualize_last_width_le_all_of_rate_strict_of_width_lt
      heq
  intro i hwidth_lt
  let wi : ℝ := levels (adjacentHighIndex i) - levels (adjacentLowIndex i)
  let wl : ℝ :=
    levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  have hlast_high :
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) = 1 := by
    simpa [lastAdjacentIndex, adjacentHighIndex, lastLevelIndex] using
      hlevels.2.1
  have hlast_low_pos :
      0 < levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
    BinaryEndpointLevelVector_last_low_pos hm hlevels
  have hone_sub_wl_pos : 0 < 1 - wl := by
    dsimp [wl]
    change
      0 <
        1 -
          (levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    linarith
  have hwl_lt_one : wl < 1 := by
    dsimp [wl]
    change
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
        1
    linarith
  have hwi_lt_wl : wi < wl := by
    simpa [wi, wl] using hwidth_lt
  have hone_sub_wi_pos : 0 < 1 - wi := by
    linarith
  have hone_sub_lt : 1 - wl < 1 - wi := by
    linarith
  have hlog :
      Real.log (1 - wl) < Real.log (1 - wi) :=
    Real.log_lt_log hone_sub_wl_pos hone_sub_lt
  have hneglog :
      -Real.log (1 - wi) < -Real.log (1 - wl) := by
    linarith
  have hrate_i :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) i ≤
        -Real.log (1 - wi) := by
    simpa [wi] using
      binaryEndpointAwareAdjacentRate_uniform_le_neg_log_one_sub_width
        hm hlevels i
  have hrate_last :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) =
        -Real.log (1 - wl) := by
    simpa [wl] using
      binaryEndpointAwareAdjacentRate_uniform_last_eq_neg_log_one_sub_width
        hm hlevels
  exact hrate_i.trans_lt (hneglog.trans_eq hrate_last.symm)

/--
Lemma C.6 lower-bound bridge with the rate-comparison premise isolated: the
source's monotone-rate argument may be supplied as a strict comparison saying
that any interval narrower than the last has smaller adjacent rate.  The
finite arithmetic then yields the endpoint lower bound.
-/
theorem BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_equalized_rate_strict_of_width_lt
    {m : ℕ} {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hrate_strict :
      ∀ i : Fin (m + 1),
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) <
            levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
              levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) →
          binaryEndpointAwareAdjacentRate levels sampleRate i <
            binaryEndpointAwareAdjacentRate levels sampleRate
              (lastAdjacentIndex : Fin (m + 1))) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_last_width_le_all
    hlevels
    (BinaryEndpointAwareAdjacentRatesEqualize_last_width_le_all_of_rate_strict_of_width_lt
      heq hrate_strict)

/--
Uniform-matching Lemma C.6 endpoint lower bound: for endpoint-normalized
levels with all adjacent rates equal under uniform sample rates, the
penultimate level is at least `1 - 1 / (number of adjacent intervals)`.
-/
theorem BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_last_width_le_all
    hlevels
    (BinaryEndpointAwareAdjacentRatesEqualize_uniform_last_width_le_all
      hm hlevels heq)

/--
Uniform-matching C.2 rate upper bound: if adjacent rates are equalized, then
the last endpoint-aware rate is at most the elementary grid rate
`-log (1 - 1/(m+1))`.
-/
theorem BinaryEndpointLevelVector_uniform_equalized_last_rate_le_neg_log_one_sub_inv
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    binaryEndpointAwareAdjacentRate levels
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin (m + 1)) ≤
      -Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) := by
  let width : ℝ :=
    levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  have hwidth_le :
      width ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
    dsimp [width]
    exact
      BinaryEndpointLevelVector_last_width_le_inv_of_last_width_le_all
        hlevels
        (BinaryEndpointAwareAdjacentRatesEqualize_uniform_last_width_le_all
          hm hlevels heq)
  have hinv_lt_one : 1 / ((m + 1 : ℕ) : ℝ) < 1 := by
    have hden_pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    have hden_gt_one : 1 < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_lt_succ hm
    rw [div_lt_one hden_pos]
    simpa using hden_gt_one
  have hmono :
      -Real.log (1 - width) ≤
        -Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) :=
    AppliedModelingLib.Math.neg_log_one_sub_mono hwidth_le hinv_lt_one
  have hrate :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) =
        -Real.log (1 - width) := by
    simpa [width] using
      binaryEndpointAwareAdjacentRate_uniform_last_eq_neg_log_one_sub_width
        hm hlevels
  exact hrate.trans_le hmono

/--
Quantitative C.2 width bound: in a uniform equalized endpoint chain, every
adjacent probability gap has square at most `1/(m+1)`.  The qualitative
adjacent-mesh convergence theorem below is often enough, but this rate is a
useful proof target for non-equispaced B.1 selector-drift arguments.
-/
theorem BinaryEndpointLevelVector_uniform_equalized_adjacent_width_sq_le_inv
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (i : Fin (m + 1)) :
    (levels (adjacentHighIndex i) - levels (adjacentLowIndex i)) ^ 2 ≤
      1 / ((m + 1 : ℕ) : ℝ) := by
  let width : ℝ :=
    levels (adjacentHighIndex i) - levels (adjacentLowIndex i)
  have hwidth_nonneg : 0 ≤ width := by
    dsimp [width]
    exact BinaryEndpointLevelVector_adjacent_width_nonneg hlevels i
  have hwidth_lt_one : width < 1 := by
    dsimp [width]
    exact BinaryEndpointLevelVector_adjacent_width_lt_one hm hlevels i
  have hwidth_sq_lt_one : width ^ 2 < 1 := by
    exact (sq_lt_one_iff₀ hwidth_nonneg).mpr hwidth_lt_one
  have hrate_lower :
      -Real.log (1 - width ^ 2) ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) i := by
    simpa [width] using
      binaryEndpointAwareAdjacentRate_uniform_ge_neg_log_one_sub_width_sq
        hm hlevels i
  have hrate_eq :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) i =
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) :=
    heq i (lastAdjacentIndex : Fin (m + 1))
  have hrate_upper :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) ≤
        -Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) :=
    BinaryEndpointLevelVector_uniform_equalized_last_rate_le_neg_log_one_sub_inv
      hm hlevels heq
  have hlog_bound :
      -Real.log (1 - width ^ 2) ≤
        -Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) := by
    exact hrate_lower.trans (hrate_eq.trans_le hrate_upper)
  have hinv_lt_one : 1 / ((m + 1 : ℕ) : ℝ) < 1 := by
    have hden_pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    have hden_gt_one : 1 < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_lt_succ hm
    rw [div_lt_one hden_pos]
    simpa using hden_gt_one
  have hinv_nonneg : 0 ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
    positivity
  have harg_left_pos : 0 < 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
    linarith
  have harg_right_pos : 0 < 1 - width ^ 2 := by
    linarith
  have hlog_le :
      Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) ≤
        Real.log (1 - width ^ 2) := by
    linarith
  have hsub_le :
      1 - 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 - width ^ 2 :=
    (Real.log_le_log_iff harg_left_pos harg_right_pos).mp hlog_le
  nlinarith [hinv_nonneg, hwidth_nonneg]

/-- The elementary grid upper rate is at most one for every nontrivial chain. -/
theorem neg_log_one_sub_inv_adjacent_count_le_one {m : ℕ} (hm : 0 < m) :
    -Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) ≤ 1 := by
  let x : ℝ := 1 / ((m + 1 : ℕ) : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x < 1 := by
    dsimp [x]
    have hone_lt : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_lt_succ hm
    have h :=
      one_div_lt_one_div_of_lt (a := (1 : ℝ))
        (b := ((m + 1 : ℕ) : ℝ)) zero_lt_one hone_lt
    simpa using h
  have hlog :
      -Real.log (1 - x) ≤ x / (1 - x) :=
    AppliedModelingLib.Math.neg_log_one_sub_le_div_self hx0 hx1
  have hx_div_le_one : x / (1 - x) ≤ 1 := by
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have hm_ge_one : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_iff.mp hm)
    have hdiv_eq : x / (1 - x) = 1 / (m : ℝ) := by
      dsimp [x]
      field_simp [ne_of_gt hm_pos]
      norm_num [Nat.cast_add, Nat.cast_one]
    have hinv_le : 1 / (m : ℝ) ≤ 1 := by
      have h :=
        one_div_le_one_div_of_le (a := (1 : ℝ)) (b := (m : ℝ))
          zero_lt_one hm_ge_one
      simpa using h
    exact hdiv_eq.trans_le hinv_le
  exact hlog.trans hx_div_le_one

/--
For a uniform equalized endpoint chain, the C.7 lower-bound side condition
`(1/5) * objective ≤ 1` follows from the C.6 grid-rate upper bound.
-/
theorem BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1 := by
  have hobj_eq :
      binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) :=
    by
      unfold binaryEndpointAwareAdjacentRateObjective
      exact
        AppliedModelingLib.finiteMin_eq_of_forall
          (binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ)))
          (binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)))
          (fun i => heq i (lastAdjacentIndex : Fin (m + 1)))
  have hobj_le_one :
      binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1 := by
    calc
      binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          =
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) := hobj_eq
      _ ≤ -Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) :=
        BinaryEndpointLevelVector_uniform_equalized_last_rate_le_neg_log_one_sub_inv
          hm hlevels heq
      _ ≤ 1 := neg_log_one_sub_inv_adjacent_count_le_one hm
  have hobj_nonneg :
      0 ≤
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    exact le_of_lt
      (by
        rw [hobj_eq]
        exact
          binaryEndpointAwareAdjacentRate_pos
            hm levels (fun _ : Fin (m + 2) => (1 : ℝ)) hlevels
            (by intro i; norm_num) (by intro i; norm_num)
            (lastAdjacentIndex : Fin (m + 1)))
  have hmul_le :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective levels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    exact mul_le_of_le_one_left hobj_nonneg (by norm_num)
  exact hmul_le.trans hobj_le_one

/--
Corollary C.2 rate consequence: along any sequence of endpoint-normalized
uniform equalized level vectors with `N+1` adjacent interior intervals, the
common last adjacent rate tends to zero.
-/
theorem corollaryC2_uniform_equalized_last_rate_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        binaryEndpointAwareAdjacentRate (levels N)
          (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((N + 1) + 1)))
      atTop (nhds 0) := by
  have hupper :
      Tendsto
        (fun N : ℕ =>
          -Real.log (1 - 1 / ((((N + 1) + 1 : ℕ) : ℝ))))
        atTop (nhds 0) := by
    have hcomp :=
      AppliedModelingLib.Math.tendsto_neg_log_one_sub_inv_nat_succ_nhds_zero.comp
        (tendsto_add_atTop_nat 1)
    refine Tendsto.congr' ?_ hcomp
    filter_upwards with N
    norm_num [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper ?_ ?_
  · filter_upwards with N
    exact
      le_of_lt
        (binaryEndpointAwareAdjacentRate_pos
          (hm := Nat.succ_pos N)
          (levels N)
          (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
          (hlevels N)
          (by intro i; norm_num)
          (by intro i; norm_num)
          (lastAdjacentIndex : Fin ((N + 1) + 1)))
  · filter_upwards with N
    exact
      BinaryEndpointLevelVector_uniform_equalized_last_rate_le_neg_log_one_sub_inv
        (hm := Nat.succ_pos N)
        (hlevels N)
        (heq N)

/-- Maximum adjacent width of an endpoint-normalized binary-rating grid. -/
noncomputable def binaryEndpointAdjacentMaxWidth
    {m : ℕ} (levels : Fin (m + 2) → ℝ) : ℝ :=
  AppliedModelingLib.finiteMax
    (fun i : Fin (m + 1) =>
      levels (adjacentHighIndex i) - levels (adjacentLowIndex i))

/-- The adjacent-width maximum is nonnegative for endpoint level vectors. -/
theorem binaryEndpointAdjacentMaxWidth_nonneg
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels) :
    0 ≤ binaryEndpointAdjacentMaxWidth levels := by
  let i0 : Fin (m + 1) := ⟨0, by omega⟩
  exact
    (BinaryEndpointLevelVector_adjacent_width_nonneg hlevels i0).trans
      (AppliedModelingLib.le_finiteMax
        (fun i : Fin (m + 1) =>
          levels (adjacentHighIndex i) - levels (adjacentLowIndex i))
        i0)

/--
Quantitative C.2 bound for the largest adjacent gap in a uniform equalized
endpoint chain.
-/
theorem binaryEndpointAdjacentMaxWidth_sq_le_inv_of_uniform_equalized
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (binaryEndpointAdjacentMaxWidth levels) ^ 2 ≤
      1 / ((m + 1 : ℕ) : ℝ) := by
  obtain ⟨i, hmax_eq⟩ :=
    AppliedModelingLib.exists_finiteMax_eq
      (fun i : Fin (m + 1) =>
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i))
  simpa [binaryEndpointAdjacentMaxWidth, hmax_eq] using
    BinaryEndpointLevelVector_uniform_equalized_adjacent_width_sq_le_inv
      hm hlevels heq i

/--
Corollary C.2 mesh consequence: along any sequence of endpoint-normalized
uniform equalized level vectors, the largest adjacent grid width tends to zero.
-/
theorem corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        binaryEndpointAdjacentMaxWidth (m := N + 1) (levels N))
      atTop (nhds 0) := by
  have hrate_tendsto :=
    corollaryC2_uniform_equalized_last_rate_tendsto_zero
      levels hlevels heq
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards with N
    have hmax_nonneg :
        0 ≤ binaryEndpointAdjacentMaxWidth (m := N + 1) (levels N) :=
      binaryEndpointAdjacentMaxWidth_nonneg (hlevels N)
    exact lt_of_lt_of_le ha hmax_nonneg
  · intro b hb
    let ε : ℝ := min b (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact lt_min hb (by norm_num)
    have hε_lt_one : ε < 1 := by
      dsimp [ε]
      exact lt_of_le_of_lt (min_le_right b (1 / 2 : ℝ)) (by norm_num)
    have hε_le_b : ε ≤ b := by
      dsimp [ε]
      exact min_le_left b (1 / 2 : ℝ)
    let η : ℝ := -Real.log (1 - ε ^ 2)
    have hη_pos : 0 < η := by
      dsimp [η]
      exact AppliedModelingLib.Math.neg_log_one_sub_sq_pos hε_pos hε_lt_one
    have hevent :
        ∀ᶠ N : ℕ in atTop,
          binaryEndpointAwareAdjacentRate (levels N)
              (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
              (lastAdjacentIndex : Fin ((N + 1) + 1)) < η :=
      hrate_tendsto.eventually (eventually_lt_nhds hη_pos)
    filter_upwards [hevent] with N hrate_lt
    by_contra hnot
    have hmax_ge :
        b ≤ binaryEndpointAdjacentMaxWidth (m := N + 1) (levels N) :=
      le_of_not_gt hnot
    obtain ⟨i, hmax_eq⟩ :=
      AppliedModelingLib.exists_finiteMax_eq
        (fun i : Fin ((N + 1) + 1) =>
          levels N (adjacentHighIndex i) -
            levels N (adjacentLowIndex i))
    have hwidth_ge_b :
        b ≤
          levels N (adjacentHighIndex i) -
            levels N (adjacentLowIndex i) := by
      simpa [binaryEndpointAdjacentMaxWidth, hmax_eq] using hmax_ge
    have hgap :
        ε ≤
          levels N (adjacentHighIndex i) -
            levels N (adjacentLowIndex i) :=
      hε_le_b.trans hwidth_ge_b
    have hrate_ge :
        η ≤
          binaryEndpointAwareAdjacentRate (levels N)
            (fun _ : Fin ((N + 1) + 2) => (1 : ℝ)) i := by
      dsimp [η]
      exact
        binaryEndpointAwareAdjacentRate_uniform_gap_ge_neg_log_one_sub_sq
          hε_pos (hm := Nat.succ_pos N) (hlevels N) i hgap
    have hrate_eq :
        binaryEndpointAwareAdjacentRate (levels N)
            (fun _ : Fin ((N + 1) + 2) => (1 : ℝ)) i =
          binaryEndpointAwareAdjacentRate (levels N)
            (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((N + 1) + 1)) :=
      heq N i (lastAdjacentIndex : Fin ((N + 1) + 1))
    have hη_le_last :
        η ≤
          binaryEndpointAwareAdjacentRate (levels N)
            (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((N + 1) + 1)) := by
      simpa [hrate_eq] using hrate_ge
    exact not_lt_of_ge hη_le_last hrate_lt

/--
Uniform-matching Lemma C.6 half-bound used at the start of Lemma C.7:
equalized adjacent rates imply the penultimate level is at least `1/2`.
-/
theorem BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_half
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (1 / 2 : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
  exact
    (one_half_le_one_sub_inv_adjacent_count hm).trans
      (BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        hm hlevels heq)

/--
Lemma C.7 algebraic endpoint-refinement step.  In the uniform equalized case,
Lemma C.6 gives the old penultimate level `t` at least `1/2`; replacing the
endpoint by `(1 + sqrt t) / 2` loses at most a factor five in the last
negative-log rate.
-/
theorem BinaryEndpointLevelVector_uniform_refined_last_rate_ge_one_fifth
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {refinedLastLow : ℝ}
    (hrefined :
      refinedLastLow =
        (1 +
          Real.sqrt
            (levels
              (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))) / 2) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) ≤
      -Real.log refinedLastLow := by
  let t : ℝ :=
    levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  have ht_half : (1 / 2 : ℝ) ≤ t := by
    dsimp [t]
    exact BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_half
      hm hlevels heq
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    exact BinaryEndpointLevelVector_le_one hlevels
      (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  have hlog :
      (1 / 5 : ℝ) * (-Real.log t) ≤
        -Real.log ((1 + Real.sqrt t) / 2) :=
    AppliedModelingLib.Math.neg_log_one_add_sqrt_div_two_ge_one_fifth_neg_log
      ht_half ht_le_one
  have hrate :
      binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) =
        -Real.log t := by
    have hlast :=
      binaryEndpointAwareAdjacentRate_uniform_last_eq_neg_log_one_sub_width
      hm hlevels
    have hhigh :
        levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) = 1 := by
      simpa [lastAdjacentIndex, adjacentHighIndex, lastLevelIndex] using
        hlevels.2.1
    rw [hlast, hhigh]
    dsimp [t]
    ring_nf
  simpa [t, hrefined, hrate] using hlog

/--
C.8 endpoint step: a lower bound on the first endpoint-aware rate gives a
linear lower bound on the first interior level under uniform matching.
-/
theorem BinaryEndpointLevelVector_uniform_first_level_ge_half_of_first_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_first :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (m + 1))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  let t : ℝ :=
    levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
  let r : ℝ :=
    binaryEndpointAwareAdjacentRate levels
      (fun _ : Fin (m + 2) => (1 : ℝ))
      (firstAdjacentIndex : Fin (m + 1))
  have ht_lt_one : t < 1 := by
    dsimp [t]
    exact BinaryEndpointLevelVector_lt_one_of_not_last hlevels
      (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      (by
        simp [firstAdjacentIndex, adjacentHighIndex]
        omega)
  have hrate : r = -Real.log (1 - t) := by
    dsimp [r, t]
    have hfirst :=
      binaryEndpointAwareAdjacentRate_first
        levels (fun _ : Fin (m + 2) => (1 : ℝ))
        (firstAdjacentIndex : Fin (m + 1)) (by simp)
    simpa [firstAdjacentIndex, adjacentHighIndex] using hfirst
  have htail : 1 - Real.exp (-r) = t := by
    have hpos : 0 < 1 - t := by linarith
    rw [hrate]
    rw [neg_neg, Real.exp_log hpos]
    ring
  have hlower_le_r : lower ≤ r := by
    simpa [r] using hlower_le_first
  have hbound :=
    AppliedModelingLib.Math.half_lower_le_one_sub_exp_neg_of_lower_le_rate
      hlower0 hlower1 hlower_le_r
  rwa [htail] at hbound

/--
C.8 endpoint step in equalized form: for a uniform equalized chain, any lower
bound on the last adjacent rate also lower-bounds the first interior level.
-/
theorem BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_last_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_last :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  have hfirst :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (m + 1)) := by
    calc
      lower ≤
          binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) := hlower_le_last
      _ =
          binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (m + 1)) :=
            heq (lastAdjacentIndex : Fin (m + 1))
              (firstAdjacentIndex : Fin (m + 1))
  exact
    BinaryEndpointLevelVector_uniform_first_level_ge_half_of_first_rate_lower
      hm hlevels hlower0 hlower1 hfirst

/--
C.8 endpoint step in equalized objective form: for a uniform equalized chain,
any lower bound on the finite worst-adjacent objective lower-bounds the first
interior level.
-/
theorem BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_objective_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_objective :
      lower ≤
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  have hobj :
      binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) :=
    by
      unfold binaryEndpointAwareAdjacentRateObjective
      exact
        AppliedModelingLib.finiteMin_eq_of_forall
          (binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ)))
          (binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)))
          (fun i => heq i (lastAdjacentIndex : Fin (m + 1)))
  have hlower_le_last :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) := by
    simpa [hobj] using hlower_le_objective
  exact
    BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_last_rate_lower
      hm hlevels heq hlower0 hlower1 hlower_le_last

/--
Lemma C.5 first endpoint split algebra: the split
`(1 - sqrt (1 - pHi)) / 2` makes the endpoint rate from zero equal to the
uniform closed threshold rate to `pHi`.
-/
theorem lemmaC5_uniform_firstEndpointEqualSplit_rate_eq
    {pHi : ℝ} (hpHi0 : 0 ≤ pHi) (hpHi1 : pHi ≤ 1) :
    -Real.log (1 - bernoulliFirstEndpointEqualSplit pHi) =
      weightedBernoulliClosedThresholdRate 1 1 pHi
        (bernoulliFirstEndpointEqualSplit pHi) := by
  exact
    (weightedBernoulliClosedThresholdRate_one_one_firstEndpointEqualSplit_eq
      hpHi0 hpHi1).symm

/--
Lemma C.5 interior split algebra: the Hellinger split inside an interval
equalizes the two adjacent uniform closed threshold rates.
-/
theorem lemmaC5_uniform_interiorEqualSplit_rate_eq
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliInteriorEqualSplit pLo pHi) pLo =
      weightedBernoulliClosedThresholdRate 1 1 pHi
        (bernoulliInteriorEqualSplit pLo pHi) :=
  weightedBernoulliClosedThresholdRate_one_one_interiorEqualSplit_eq
    hpLo0 hpHi1 hlt

/--
Lemma C.5 last endpoint split algebra: the split `(1 + sqrt pLo) / 2` makes
the uniform closed threshold rate from `pLo` equal to the endpoint rate to one.
-/
theorem lemmaC5_uniform_lastEndpointEqualSplit_rate_eq
    {pLo : ℝ} (hpLo0 : 0 ≤ pLo) (hpLo1 : pLo ≤ 1) :
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliLastEndpointEqualSplit pLo) pLo =
      -Real.log (bernoulliLastEndpointEqualSplit pLo) :=
  weightedBernoulliClosedThresholdRate_one_one_lastEndpointEqualSplit_eq
    hpLo0 hpLo1

/--
Lemma C.5 doubled-chain level constructor for uniform matching.  Even refined
indices copy the old chain; odd refined indices use the endpoint split at the
two ends and the Hellinger interior split in the middle.
-/
def uniformDoubledEndpointLevels {m : ℕ}
    (oldLevels : Fin (m + 2) → ℝ) : Fin ((2 * m + 1) + 2) → ℝ :=
  fun i =>
    if hEven : i.val % 2 = 0 then
      oldLevels ⟨i.val / 2, by omega⟩
    else if hFirst : i.val = 1 then
      bernoulliFirstEndpointEqualSplit
        (oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    else if hLast : i.val = 2 * m + 1 then
      bernoulliLastEndpointEqualSplit
        (oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    else
      bernoulliInteriorEqualSplit
        (oldLevels ⟨i.val / 2, by omega⟩)
        (oldLevels ⟨i.val / 2 + 1, by omega⟩)

/-- Even refined indices in the C.5 doubled chain copy the old levels. -/
theorem uniformDoubledEndpointLevels_even
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) (i : Fin (m + 2)) :
    uniformDoubledEndpointLevels oldLevels
        ⟨2 * i.val, by omega⟩ = oldLevels i := by
  unfold uniformDoubledEndpointLevels
  simp

/-- The first odd refined index has the source's endpoint split formula. -/
theorem uniformDoubledEndpointLevels_first_odd
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) :
    uniformDoubledEndpointLevels oldLevels
        (⟨1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliFirstEndpointEqualSplit
        (oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) := by
  unfold uniformDoubledEndpointLevels
  simp

/-- The last odd refined index has the source's endpoint split formula. -/
theorem uniformDoubledEndpointLevels_last_odd
    {m : ℕ} (hm : 0 < m) (oldLevels : Fin (m + 2) → ℝ) :
    uniformDoubledEndpointLevels oldLevels
        (⟨2 * m + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliLastEndpointEqualSplit
        (oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) := by
  unfold uniformDoubledEndpointLevels
  simp [hm.ne']

/-- Middle odd refined indices use the Hellinger interior split. -/
theorem uniformDoubledEndpointLevels_middle_odd
    {m k : ℕ} (hk0 : 0 < k) (hkm : k < m)
    (oldLevels : Fin (m + 2) → ℝ) :
    uniformDoubledEndpointLevels oldLevels
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliInteriorEqualSplit
        (oldLevels ⟨k, by omega⟩)
        (oldLevels ⟨k + 1, by omega⟩) := by
  unfold uniformDoubledEndpointLevels
  have hdiv : (2 * k + 1) / 2 = k := by
    rw [show 2 * k + 1 = 1 + 2 * k by omega]
    simp [Nat.add_mul_div_left]
  simp [hdiv, Nat.ne_of_gt hk0, ne_of_lt hkm]

/-- The first odd C.5 doubled level lies in the first old adjacent interval. -/
theorem uniformDoubledEndpointLevels_first_odd_mem_Icc
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    uniformDoubledEndpointLevels oldLevels
        (⟨1, by omega⟩ : Fin ((2 * m + 1) + 2)) ∈
      Set.Icc (oldLevels ⟨0, by omega⟩) (oldLevels ⟨1, by omega⟩) := by
  have hpHi0 :
      0 < oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
    BinaryEndpointLevelVector_pos_of_not_first hold
      (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) (by
        simp [adjacentHighIndex, firstAdjacentIndex])
  have hpHi1 :
      oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤ 1 :=
    BinaryEndpointLevelVector_le_one hold
      (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
  have hmem :=
    bernoulliFirstEndpointEqualSplit_mem_Ioo hpHi0 hpHi1
  have hzero : oldLevels ⟨0, by omega⟩ = 0 := by
    simpa [firstLevelIndex] using hold.1
  rw [uniformDoubledEndpointLevels_first_odd]
  constructor
  · rw [hzero]
    exact hmem.1.le
  · simpa [firstAdjacentIndex, adjacentHighIndex] using hmem.2.le

/-- Middle odd C.5 doubled levels lie in their old adjacent intervals. -/
theorem uniformDoubledEndpointLevels_middle_odd_mem_Icc
    {m k : ℕ} (hk0 : 0 < k) (hkm : k < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    uniformDoubledEndpointLevels oldLevels
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) ∈
      Set.Icc (oldLevels ⟨k, by omega⟩) (oldLevels ⟨k + 1, by omega⟩) := by
  have hpLo0 : 0 ≤ oldLevels ⟨k, by omega⟩ :=
    BinaryEndpointLevelVector_nonneg hold ⟨k, by omega⟩
  have hpHi1 : oldLevels ⟨k + 1, by omega⟩ ≤ 1 :=
    BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
  have hlt : oldLevels ⟨k, by omega⟩ < oldLevels ⟨k + 1, by omega⟩ := by
    simpa [adjacentLowIndex, adjacentHighIndex] using
      hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
  have hmem :=
    bernoulliInteriorEqualSplit_mem_Ioo hpLo0 hpHi1 hlt
  rw [uniformDoubledEndpointLevels_middle_odd hk0 hkm]
  exact ⟨hmem.1.le, hmem.2.le⟩

/-- The last odd C.5 doubled level lies in the last old adjacent interval. -/
theorem uniformDoubledEndpointLevels_last_odd_mem_Icc
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    uniformDoubledEndpointLevels oldLevels
        (⟨2 * m + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) ∈
      Set.Icc (oldLevels ⟨m, by omega⟩) (oldLevels ⟨m + 1, by omega⟩) := by
  have hpLo0 :
      0 ≤ oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
    BinaryEndpointLevelVector_nonneg hold
      (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  have hpLo1 :
      oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) < 1 :=
    BinaryEndpointLevelVector_lt_one_of_not_last hold
      (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) (by
        simp [lastAdjacentIndex, adjacentLowIndex])
  have hmem :=
    bernoulliLastEndpointEqualSplit_mem_Ioo hpLo0 hpLo1
  have hone : oldLevels ⟨m + 1, by omega⟩ = 1 := by
    simpa [lastLevelIndex] using hold.2.1
  rw [uniformDoubledEndpointLevels_last_odd hm]
  constructor
  · simpa [lastAdjacentIndex, adjacentLowIndex] using hmem.1.le
  · rw [hone]
    exact hmem.2.le

/--
Every odd C.5 doubled level lies in some old two-step level bracket.  This is
the one-step local inclusion used when iterating the B.1 dyadic construction.
-/
theorem uniformDoubledEndpointLevels_odd_mem_two_step_interval
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    ∃ i : Fin m,
      uniformDoubledEndpointLevels oldLevels
          (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) ∈
        Set.Icc (oldLevels ⟨i.1, by omega⟩)
          (oldLevels ⟨i.1 + 2, by omega⟩) := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨⟨0, hm⟩, ?_⟩
    have hmem := uniformDoubledEndpointLevels_first_odd_mem_Icc hm hold
    constructor
    · simpa using hmem.1
    · have hright :
          oldLevels ⟨1, by omega⟩ ≤ oldLevels ⟨2, by omega⟩ :=
        BinaryEndpointLevelVector_mono
          (a := (⟨1, by omega⟩ : Fin (m + 2)))
          (b := (⟨2, by omega⟩ : Fin (m + 2))) hold
          (show (1 : ℕ) ≤ 2 by omega)
      exact hmem.2.trans hright
  · by_cases hkm : k = m
    · subst k
      refine ⟨⟨m - 1, by omega⟩, ?_⟩
      have hmem := uniformDoubledEndpointLevels_last_odd_mem_Icc hm hold
      constructor
      · have hleft :
            oldLevels ⟨m - 1, by omega⟩ ≤ oldLevels ⟨m, by omega⟩ :=
          BinaryEndpointLevelVector_mono
            (a := (⟨m - 1, by omega⟩ : Fin (m + 2)))
            (b := (⟨m, by omega⟩ : Fin (m + 2))) hold
            (show m - 1 ≤ m by omega)
        exact hleft.trans hmem.1
      · have hidx : m - 1 + 2 = m + 1 := by omega
        simpa [hidx] using hmem.2
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkm_lt : k < m := lt_of_le_of_ne hk hkm
      refine ⟨⟨k, hkm_lt⟩, ?_⟩
      have hmem :=
        uniformDoubledEndpointLevels_middle_odd_mem_Icc hkpos hkm_lt hold
      constructor
      · simpa using hmem.1
      · have hright :
            oldLevels ⟨k + 1, by omega⟩ ≤ oldLevels ⟨k + 2, by omega⟩ :=
          BinaryEndpointLevelVector_mono
            (a := (⟨k + 1, by omega⟩ : Fin (m + 2)))
            (b := (⟨k + 2, by omega⟩ : Fin (m + 2))) hold
            (show k + 1 ≤ k + 2 by omega)
        exact hmem.2.trans hright

/-- Every even C.5 doubled level lies in some old two-step level bracket. -/
theorem uniformDoubledEndpointLevels_even_mem_two_step_interval
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m + 1)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    ∃ i : Fin m,
      uniformDoubledEndpointLevels oldLevels
          (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 2)) ∈
        Set.Icc (oldLevels ⟨i.1, by omega⟩)
          (oldLevels ⟨i.1 + 2, by omega⟩) := by
  have heven :
      uniformDoubledEndpointLevels oldLevels
          (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 2)) =
        oldLevels ⟨k, by omega⟩ := by
    simpa using
      uniformDoubledEndpointLevels_even oldLevels
        (⟨k, by omega⟩ : Fin (m + 2))
  by_cases hk0 : k = 0
  · subst k
    refine ⟨⟨0, hm⟩, ?_⟩
    rw [heven]
    constructor
    · rfl
    · exact
        BinaryEndpointLevelVector_mono
          (a := (⟨0, by omega⟩ : Fin (m + 2)))
          (b := (⟨2, by omega⟩ : Fin (m + 2))) hold
          (show (0 : ℕ) ≤ 2 by omega)
  · by_cases hktop : k = m + 1
    · subst k
      refine ⟨⟨m - 1, by omega⟩, ?_⟩
      rw [heven]
      constructor
      · exact
          BinaryEndpointLevelVector_mono
            (a := (⟨m - 1, by omega⟩ : Fin (m + 2)))
            (b := (⟨m + 1, by omega⟩ : Fin (m + 2))) hold
            (show m - 1 ≤ m + 1 by omega)
      · have hidx : m - 1 + 2 = m + 1 := by omega
        simp [hidx]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hklt_top : k < m + 1 := lt_of_le_of_ne hk hktop
      refine ⟨⟨k - 1, by omega⟩, ?_⟩
      rw [heven]
      constructor
      · exact
          BinaryEndpointLevelVector_mono
            (a := (⟨k - 1, by omega⟩ : Fin (m + 2)))
            (b := (⟨k, by omega⟩ : Fin (m + 2))) hold
            (show k - 1 ≤ k by omega)
      · have hidx : k - 1 + 2 = k + 1 := by omega
        have hright :
            oldLevels ⟨k, by omega⟩ ≤ oldLevels ⟨k + 1, by omega⟩ :=
          BinaryEndpointLevelVector_mono
            (a := (⟨k, by omega⟩ : Fin (m + 2)))
            (b := (⟨k + 1, by omega⟩ : Fin (m + 2))) hold
            (show k ≤ k + 1 by omega)
        simpa [hidx] using hright

/--
Every C.5 doubled level lies in an old two-step level bracket.  This packages
the parity split of the doubled construction into the bracket form used by
the B.1 mesh argument.
-/
theorem uniformDoubledEndpointLevels_mem_two_step_interval
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (r : Fin ((2 * m + 1) + 2)) :
    ∃ i : Fin m,
      uniformDoubledEndpointLevels oldLevels r ∈
        Set.Icc (oldLevels ⟨i.1, by omega⟩)
          (oldLevels ⟨i.1 + 2, by omega⟩) := by
  by_cases heven : r.1 % 2 = 0
  · let k : ℕ := r.1 / 2
    have hk : k ≤ m + 1 := by
      dsimp [k]
      omega
    have hr_eq :
        r = (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 2)) := by
      ext
      dsimp [k]
      omega
    simpa [hr_eq] using
      uniformDoubledEndpointLevels_even_mem_two_step_interval
        (m := m) (k := k) hm hk hold
  · let k : ℕ := r.1 / 2
    have hmod_one : r.1 % 2 = 1 := by
      have hmod_lt : r.1 % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    have hk : k ≤ m := by
      dsimp [k]
      omega
    have hr_eq :
        r = (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) := by
      ext
      dsimp [k]
      omega
    simpa [hr_eq] using
      uniformDoubledEndpointLevels_odd_mem_two_step_interval
        (m := m) (k := k) hm hk hold

/--
Indexed C.5 local inclusion: if a refined index lies in the three-point window
`{2*i, 2*i+1, 2*i+2}`, its refined level lies in the old two-step bracket
`[t_i, t_{i+2}]`.  This is the index-specific form needed in the B.1 floor
argument.
-/
theorem uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (i : Fin m) (r : Fin ((2 * m + 1) + 2))
    (hlo : 2 * i.1 ≤ r.1) (hhi : r.1 ≤ 2 * i.1 + 2) :
    uniformDoubledEndpointLevels oldLevels r ∈
      Set.Icc (oldLevels ⟨i.1, by omega⟩)
        (oldLevels ⟨i.1 + 2, by omega⟩) := by
  have hcases :
      r.1 = 2 * i.1 ∨ r.1 = 2 * i.1 + 1 ∨
        r.1 = 2 * i.1 + 2 := by
    omega
  rcases hcases with hcase | hcase | hcase
  · have hr_eq :
        r = (⟨2 * i.1, by omega⟩ : Fin ((2 * m + 1) + 2)) := by
      ext
      exact hcase
    rw [hr_eq]
    have hcopy :=
      uniformDoubledEndpointLevels_even oldLevels
        (⟨i.1, by omega⟩ : Fin (m + 2))
    rw [hcopy]
    constructor
    · rfl
    · exact
        BinaryEndpointLevelVector_mono
          (a := (⟨i.1, by omega⟩ : Fin (m + 2)))
          (b := (⟨i.1 + 2, by omega⟩ : Fin (m + 2))) hold
          (show i.1 ≤ i.1 + 2 by omega)
  · have hr_eq :
        r = (⟨2 * i.1 + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) := by
      ext
      exact hcase
    rw [hr_eq]
    by_cases hi0 : i.1 = 0
    · have hmem := uniformDoubledEndpointLevels_first_odd_mem_Icc hm hold
      constructor
      · simpa [hi0] using hmem.1
      · have hright :
            oldLevels ⟨1, by omega⟩ ≤ oldLevels ⟨2, by omega⟩ :=
          BinaryEndpointLevelVector_mono
            (a := (⟨1, by omega⟩ : Fin (m + 2)))
            (b := (⟨2, by omega⟩ : Fin (m + 2))) hold
            (show (1 : ℕ) ≤ 2 by omega)
        exact (by simpa [hi0] using hmem.2.trans hright)
    · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi0
      have him : i.1 < m := i.2
      have hmem :=
        uniformDoubledEndpointLevels_middle_odd_mem_Icc hipos him hold
      constructor
      · simpa using hmem.1
      · have hright :
            oldLevels ⟨i.1 + 1, by omega⟩ ≤
              oldLevels ⟨i.1 + 2, by omega⟩ :=
          BinaryEndpointLevelVector_mono
            (a := (⟨i.1 + 1, by omega⟩ : Fin (m + 2)))
            (b := (⟨i.1 + 2, by omega⟩ : Fin (m + 2))) hold
            (show i.1 + 1 ≤ i.1 + 2 by omega)
        exact hmem.2.trans hright
  · have hr_eq :
        r = (⟨2 * (i.1 + 1), by omega⟩ : Fin ((2 * m + 1) + 2)) := by
      ext
      omega
    rw [hr_eq]
    have hcopy :=
      uniformDoubledEndpointLevels_even oldLevels
        (⟨i.1 + 1, by omega⟩ : Fin (m + 2))
    rw [hcopy]
    constructor
    · exact
        BinaryEndpointLevelVector_mono
          (a := (⟨i.1, by omega⟩ : Fin (m + 2)))
          (b := (⟨i.1 + 1, by omega⟩ : Fin (m + 2))) hold
          (show i.1 ≤ i.1 + 1 by omega)
    · exact
        BinaryEndpointLevelVector_mono
          (a := (⟨i.1 + 1, by omega⟩ : Fin (m + 2)))
          (b := (⟨i.1 + 2, by omega⟩ : Fin (m + 2))) hold
          (show i.1 + 1 ≤ i.1 + 2 by omega)

/--
Four-point indexed C.5 inclusion matching the source floor-window arithmetic:
if a refined index lies in `{2*i, 2*i+1, 2*i+2, 2*i+3}`, its level lies in the
old two-step bracket `[t_i, t_{i+2}]`.
-/
theorem uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between_four
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (i : Fin m) (r : Fin ((2 * m + 1) + 2))
    (hlo : 2 * i.1 ≤ r.1) (hhi : r.1 ≤ 2 * i.1 + 3) :
    uniformDoubledEndpointLevels oldLevels r ∈
      Set.Icc (oldLevels ⟨i.1, by omega⟩)
        (oldLevels ⟨i.1 + 2, by omega⟩) := by
  by_cases hsmall : r.1 ≤ 2 * i.1 + 2
  · exact
      uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between
        hm hold i r hlo hsmall
  · have hcase : r.1 = 2 * i.1 + 3 := by omega
    have hr_eq :
        r = (⟨2 * (i.1 + 1) + 1, by omega⟩ :
          Fin ((2 * m + 1) + 2)) := by
      ext
      omega
    rw [hr_eq]
    by_cases hlast : i.1 + 1 = m
    · have hodd_eq :
          (⟨2 * (i.1 + 1) + 1, by omega⟩ :
              Fin ((2 * m + 1) + 2)) =
            (⟨2 * m + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) := by
        ext
        change 2 * (i.1 + 1) + 1 = 2 * m + 1
        omega
      rw [hodd_eq]
      have hmem := uniformDoubledEndpointLevels_last_odd_mem_Icc hm hold
      constructor
      · have hleft :
            oldLevels ⟨i.1, by omega⟩ ≤ oldLevels ⟨m, by omega⟩ :=
          BinaryEndpointLevelVector_mono
            (a := (⟨i.1, by omega⟩ : Fin (m + 2)))
            (b := (⟨m, by omega⟩ : Fin (m + 2))) hold
            (show i.1 ≤ m by omega)
        exact hleft.trans hmem.1
      · have hidx : i.1 + 2 = m + 1 := by omega
        simpa [hidx] using hmem.2
    · have hkpos : 0 < i.1 + 1 := by omega
      have hklt : i.1 + 1 < m := by omega
      have hmem :=
        uniformDoubledEndpointLevels_middle_odd_mem_Icc hkpos hklt hold
      constructor
      · have hleft :
            oldLevels ⟨i.1, by omega⟩ ≤
              oldLevels ⟨i.1 + 1, by omega⟩ :=
          BinaryEndpointLevelVector_mono
            (a := (⟨i.1, by omega⟩ : Fin (m + 2)))
            (b := (⟨i.1 + 1, by omega⟩ : Fin (m + 2))) hold
            (show i.1 ≤ i.1 + 1 by omega)
        exact hleft.trans hmem.1
      · simpa using hmem.2

/--
Five-point indexed C.5 inclusion.  This adds the copied even endpoint
`2*i+4 = 2*(i+2)` to the four-point source window; it is needed for clamped
floor selectors at the right endpoint.
-/
theorem uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between_five
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (i : Fin m) (r : Fin ((2 * m + 1) + 2))
    (hlo : 2 * i.1 ≤ r.1) (hhi : r.1 ≤ 2 * i.1 + 4) :
    uniformDoubledEndpointLevels oldLevels r ∈
      Set.Icc (oldLevels ⟨i.1, by omega⟩)
        (oldLevels ⟨i.1 + 2, by omega⟩) := by
  by_cases hsmall : r.1 ≤ 2 * i.1 + 3
  · exact
      uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between_four
        hm hold i r hlo hsmall
  · have hcase : r.1 = 2 * i.1 + 4 := by omega
    have hr_eq :
        r = (⟨2 * (i.1 + 2), by omega⟩ :
          Fin ((2 * m + 1) + 2)) := by
      ext
      omega
    rw [hr_eq]
    have hcopy :=
      uniformDoubledEndpointLevels_even oldLevels
        (⟨i.1 + 2, by omega⟩ : Fin (m + 2))
    rw [hcopy]
    constructor
    · exact
        BinaryEndpointLevelVector_mono
          (a := (⟨i.1, by omega⟩ : Fin (m + 2)))
          (b := (⟨i.1 + 2, by omega⟩ : Fin (m + 2))) hold
          (show i.1 ≤ i.1 + 2 by omega)
    · rfl

/--
In the C.5 doubled chain, every even refined edge is ordered.  The proof is
the three-way split from the source construction: first endpoint, interior
Hellinger split, and last endpoint.
-/
theorem uniformDoubledEndpointLevels_even_adjacent_ordered
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    uniformDoubledEndpointLevels oldLevels
        (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 2)) <
      uniformDoubledEndpointLevels oldLevels
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) := by
  by_cases hk0 : k = 0
  · subst k
    have hpHi0 :
        0 <
          oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
      BinaryEndpointLevelVector_pos_of_not_first hold
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) (by
          simp [adjacentHighIndex, firstAdjacentIndex])
    have hpHi1 :
        oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤ 1 :=
      BinaryEndpointLevelVector_le_one hold
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
    have hmem :=
      bernoulliFirstEndpointEqualSplit_mem_Ioo hpHi0 hpHi1
    have hleft :
        uniformDoubledEndpointLevels oldLevels
            (⟨2 * 0, by omega⟩ : Fin ((2 * m + 1) + 2)) = 0 := by
      have hcopy :=
        uniformDoubledEndpointLevels_even oldLevels
          (firstLevelIndex : Fin (m + 2))
      simpa [firstLevelIndex] using hcopy.trans hold.1
    have hright :
        uniformDoubledEndpointLevels oldLevels
            (⟨2 * 0 + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
          bernoulliFirstEndpointEqualSplit
            (oldLevels
              (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) := by
      simpa using uniformDoubledEndpointLevels_first_odd oldLevels
    rw [hleft, hright]
    exact hmem.1
  · by_cases hkm_eq : k = m
    · subst k
      have hpLo0 :
          0 ≤
            oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
        BinaryEndpointLevelVector_nonneg hold
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
      have hpLo1 :
          oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last hold
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) (by
            simp [adjacentLowIndex, lastAdjacentIndex])
      have hmem :=
        bernoulliLastEndpointEqualSplit_mem_Ioo hpLo0 hpLo1
      have hnot_first : 2 * m + 1 ≠ 1 := by omega
      simpa [uniformDoubledEndpointLevels, lastAdjacentIndex,
        adjacentLowIndex, hnot_first, hm.ne'] using hmem.1
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkm : k < m := lt_of_le_of_ne hk hkm_eq
      have hpLo0 : 0 ≤ oldLevels (⟨k, by omega⟩ : Fin (m + 2)) :=
        BinaryEndpointLevelVector_nonneg hold ⟨k, by omega⟩
      have hpHi1 : oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) ≤ 1 :=
        BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
      have hlt : oldLevels (⟨k, by omega⟩ : Fin (m + 2)) <
          oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) := by
        simpa [adjacentLowIndex, adjacentHighIndex] using
          hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
      have hmem :=
        bernoulliInteriorEqualSplit_mem_Ioo hpLo0 hpHi1 hlt
      have hdiv : (2 * k + 1) / 2 = k := by
        rw [show 2 * k + 1 = 1 + 2 * k by omega]
        simp [Nat.add_mul_div_left]
      have hnot_first : 2 * k + 1 ≠ 1 := by omega
      have hnot_last : 2 * k + 1 ≠ 2 * m + 1 := by omega
      simpa [uniformDoubledEndpointLevels, hdiv, hnot_first, hnot_last, hk0,
        hkm_eq]
        using hmem.1

/--
In the C.5 doubled chain, every odd refined edge is ordered.  This is the
right-hand side of the same endpoint/interior split construction.
-/
theorem uniformDoubledEndpointLevels_odd_adjacent_ordered
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    uniformDoubledEndpointLevels oldLevels
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) <
      uniformDoubledEndpointLevels oldLevels
        (⟨2 * k + 2, by omega⟩ : Fin ((2 * m + 1) + 2)) := by
  by_cases hk0 : k = 0
  · subst k
    have hpHi0 :
        0 <
          oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
      BinaryEndpointLevelVector_pos_of_not_first hold
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) (by
          simp [adjacentHighIndex, firstAdjacentIndex])
    have hpHi1 :
        oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤ 1 :=
      BinaryEndpointLevelVector_le_one hold
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
    have hmem :=
      bernoulliFirstEndpointEqualSplit_mem_Ioo hpHi0 hpHi1
    simpa [uniformDoubledEndpointLevels, firstAdjacentIndex,
      adjacentHighIndex] using hmem.2
  · by_cases hkm_eq : k = m
    · subst k
      have hpLo0 :
          0 ≤
            oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
        BinaryEndpointLevelVector_nonneg hold
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
      have hpLo1 :
          oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last hold
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) (by
            simp [adjacentLowIndex, lastAdjacentIndex])
      have hmem :=
        bernoulliLastEndpointEqualSplit_mem_Ioo hpLo0 hpLo1
      have hnot_first : 2 * m + 1 ≠ 1 := by omega
      simpa [uniformDoubledEndpointLevels, lastAdjacentIndex,
        adjacentLowIndex, lastLevelIndex, hnot_first, hm.ne', hold.2.1]
        using hmem.2
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkm : k < m := lt_of_le_of_ne hk hkm_eq
      have hpLo0 : 0 ≤ oldLevels (⟨k, by omega⟩ : Fin (m + 2)) :=
        BinaryEndpointLevelVector_nonneg hold ⟨k, by omega⟩
      have hpHi1 : oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) ≤ 1 :=
        BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
      have hlt : oldLevels (⟨k, by omega⟩ : Fin (m + 2)) <
          oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) := by
        simpa [adjacentLowIndex, adjacentHighIndex] using
          hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
      have hmem :=
        bernoulliInteriorEqualSplit_mem_Ioo hpLo0 hpHi1 hlt
      have hdiv : (2 * k + 1) / 2 = k := by
        rw [show 2 * k + 1 = 1 + 2 * k by omega]
        simp [Nat.add_mul_div_left]
      have hnot_first : 2 * k + 1 ≠ 1 := by omega
      have hnot_last : 2 * k + 1 ≠ 2 * m + 1 := by omega
      simpa [uniformDoubledEndpointLevels, hdiv, hnot_first, hnot_last, hk0,
        hkm_eq]
        using hmem.2

/--
Lemma C.5 feasibility certificate: the doubled endpoint chain remains an
endpoint level vector whenever the original finite chain is one.
-/
theorem uniformDoubledEndpointLevels_isEndpointLevelVector
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
  constructor
  · have hcopy :=
      uniformDoubledEndpointLevels_even oldLevels
        (firstLevelIndex : Fin (m + 2))
    simpa [firstLevelIndex] using hcopy.trans hold.1
  constructor
  · have hcopy :=
      uniformDoubledEndpointLevels_even oldLevels
        (lastLevelIndex : Fin (m + 2))
    simpa [lastLevelIndex] using hcopy.trans hold.2.1
  · intro i
    by_cases hEven : i.val % 2 = 0
    · let k := i.val / 2
      have hi_eq : i.val = 2 * k := by
        have hdecomp := Nat.mod_add_div i.val 2
        omega
      have hk : k ≤ m := by
        have hi_lt : i.val < 2 * m + 2 := i.isLt
        omega
      have hstep :=
        uniformDoubledEndpointLevels_even_adjacent_ordered
          (m := m) (k := k) hm hk hold
      convert hstep using 2
      · ext
        simp [adjacentLowIndex]
        omega
      · ext
        simp [adjacentHighIndex]
        omega
    · have hOdd : i.val % 2 = 1 := by
        have hmod := Nat.mod_two_eq_zero_or_one i.val
        omega
      let k := i.val / 2
      have hi_eq : i.val = 2 * k + 1 := by
        have hdecomp := Nat.mod_add_div i.val 2
        omega
      have hk : k ≤ m := by
        have hi_lt : i.val < 2 * m + 2 := i.isLt
        omega
      have hstep :=
        uniformDoubledEndpointLevels_odd_adjacent_ordered
          (m := m) (k := k) hm hk hold
      convert hstep using 2
      · ext
        simp [adjacentLowIndex]
        omega
      · ext
        simp [adjacentHighIndex]
        omega

/-- C.5 rate transform induced by splitting one uniform binary interval. -/
def uniformDoubledEndpointRateTransform (r : ℝ) : ℝ :=
  -Real.log ((1 + Real.exp (-r / 2)) / 2)

/--
The C.5 rate transform is at most one quarter of the old rate.  Equivalently,
AM--GM gives `exp (-r/4) <= (1 + exp (-r/2))/2`.
-/
theorem uniformDoubledEndpointRateTransform_le_one_fourth (r : ℝ) :
    uniformDoubledEndpointRateTransform r ≤ r / 4 := by
  dsimp [uniformDoubledEndpointRateTransform]
  let z : ℝ := Real.exp (-r / 4)
  have hz_pos : 0 < z := by positivity
  have hzsq : z ^ 2 = Real.exp (-r / 2) := by
    dsimp [z]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hamgm : z ≤ (1 + Real.exp (-r / 2)) / 2 := by
    have hsq : 0 ≤ (1 - z) ^ 2 := sq_nonneg (1 - z)
    rw [sq] at hsq
    nlinarith [hzsq]
  have hlog_lower :
      -r / 4 ≤ Real.log ((1 + Real.exp (-r / 2)) / 2) := by
    have hzlog : Real.log z = -r / 4 := by
      dsimp [z]
      rw [Real.log_exp]
    rw [← hzlog]
    exact Real.log_le_log hz_pos hamgm
  calc
    -Real.log ((1 + Real.exp (-r / 2)) / 2)
        ≤ -(-r / 4) := neg_le_neg hlog_lower
    _ = r / 4 := by ring

/--
Each even refined adjacent rate in the C.5 doubled chain is the same
one-variable transform of the corresponding old adjacent rate.
-/
theorem uniformDoubledEndpointLevels_even_adjacent_rate_eq_transform
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    binaryEndpointAwareAdjacentRate
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 1)) =
      uniformDoubledEndpointRateTransform
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (⟨k, by omega⟩ : Fin (m + 1))) := by
  by_cases hk0 : k = 0
  · subst k
    let pHi : ℝ :=
      oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
    have hpHi0 : 0 < pHi := by
      dsimp [pHi]
      exact
        BinaryEndpointLevelVector_pos_of_not_first hold
          (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) (by
            simp [adjacentHighIndex, firstAdjacentIndex])
    have hpHi1 : pHi < 1 := by
      dsimp [pHi]
      exact
        BinaryEndpointLevelVector_first_high_lt_one hm hold
    have hnew :
        binaryEndpointAwareAdjacentRate
            (uniformDoubledEndpointLevels oldLevels)
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (⟨2 * 0, by omega⟩ : Fin ((2 * m + 1) + 1)) =
          -Real.log (1 - bernoulliFirstEndpointEqualSplit pHi) := by
      simpa [binaryEndpointAwareAdjacentRate, uniformDoubledEndpointLevels,
        pHi, firstAdjacentIndex, adjacentHighIndex]
    have holdRate :
        binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (⟨0, by omega⟩ : Fin (m + 1)) =
          -Real.log (1 - pHi) := by
      simpa [binaryEndpointAwareAdjacentRate, pHi, firstAdjacentIndex,
        adjacentHighIndex]
    have hexp :
        Real.exp (-(-Real.log (1 - pHi)) / 2) =
          Real.sqrt (1 - pHi) := by
      have harg : -(-Real.log (1 - pHi)) / 2 =
          Real.log (1 - pHi) / 2 := by ring
      rw [harg]
      exact AppliedModelingLib.Math.exp_log_div_two_eq_sqrt (by linarith : 0 < 1 - pHi)
    rw [hnew, holdRate, uniformDoubledEndpointRateTransform, hexp]
    congr 1
    dsimp [bernoulliFirstEndpointEqualSplit]
    ring_nf
  · by_cases hkm_eq : k = m
    · subst k
      let pLo : ℝ :=
        oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
      have hpLo0 : 0 < pLo := by
        dsimp [pLo]
        exact BinaryEndpointLevelVector_last_low_pos hm hold
      have hpLo1 : pLo < 1 := by
        dsimp [pLo]
        exact
          BinaryEndpointLevelVector_lt_one_of_not_last hold
            (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) (by
              simp [adjacentLowIndex, lastAdjacentIndex])
      have hnew :
          binaryEndpointAwareAdjacentRate
              (uniformDoubledEndpointLevels oldLevels)
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
              (⟨2 * m, by omega⟩ : Fin ((2 * m + 1) + 1)) =
            -Real.log (bernoulliLastEndpointEqualSplit pLo) := by
        have hrate :=
          lemmaC5_uniform_lastEndpointEqualSplit_rate_eq
            (le_of_lt hpLo0) (le_of_lt hpLo1)
        have hnot_even_last : 2 * m ≠ 2 * m + 1 := by omega
        have hnot_first : 2 * m + 1 ≠ 1 := by omega
        simpa [binaryEndpointAwareAdjacentRate, uniformDoubledEndpointLevels,
          pLo, lastAdjacentIndex, adjacentLowIndex, hnot_even_last,
          hnot_first, hm.ne'] using hrate
      have holdRate :
          binaryEndpointAwareAdjacentRate oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))
              (⟨m, by omega⟩ : Fin (m + 1)) =
            -Real.log pLo := by
        simpa [binaryEndpointAwareAdjacentRate, pLo, lastAdjacentIndex,
          adjacentLowIndex, hm.ne']
      have hexp :
          Real.exp (-(-Real.log pLo) / 2) = Real.sqrt pLo := by
        have harg : -(-Real.log pLo) / 2 = Real.log pLo / 2 := by ring
        rw [harg]
        exact AppliedModelingLib.Math.exp_log_div_two_eq_sqrt hpLo0
      rw [hnew, holdRate, uniformDoubledEndpointRateTransform, hexp]
      congr 1
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkm : k < m := lt_of_le_of_ne hk hkm_eq
      let pLo : ℝ := oldLevels (⟨k, by omega⟩ : Fin (m + 2))
      let pHi : ℝ := oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2))
      have hpLo0 : 0 < pLo := by
        dsimp [pLo]
        exact
          BinaryEndpointLevelVector_pos_of_not_first hold
            (⟨k, by omega⟩ : Fin (m + 2)) (by omega)
      have hpHi1 : pHi < 1 := by
        dsimp [pHi]
        exact
          BinaryEndpointLevelVector_lt_one_of_not_last hold
            (⟨k + 1, by omega⟩ : Fin (m + 2)) (by
              change k + 1 ≠ m + 1
              omega)
      have hlt : pLo < pHi := by
        dsimp [pLo, pHi]
        simpa [adjacentLowIndex, adjacentHighIndex] using
          hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
      have hrate :=
        weightedBernoulliClosedThresholdRate_one_one_interiorEqualSplit_left_eq_transform
          hpLo0 hpHi1 hlt
      have hdiv : (2 * k + 1) / 2 = k := by
        rw [show 2 * k + 1 = 1 + 2 * k by omega]
        simp [Nat.add_mul_div_left]
      have hnot_even_last : 2 * k ≠ 2 * m + 1 := by omega
      have hnot_first : 2 * k + 1 ≠ 1 := by omega
      have hnot_last : 2 * k + 1 ≠ 2 * m + 1 := by omega
      simpa [uniformDoubledEndpointRateTransform, binaryEndpointAwareAdjacentRate,
        uniformDoubledEndpointLevels, pLo, pHi, hdiv, hnot_even_last,
        hnot_first, hnot_last, hk0, hkm_eq] using hrate

/--
Lemma C.5 local rate equalization: for each old adjacent interval, the inserted
odd level makes the two refined adjacent rates equal.
-/
theorem uniformDoubledEndpointLevels_adjacent_pair_rates_equal
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    binaryEndpointAwareAdjacentRate
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 1)) =
      binaryEndpointAwareAdjacentRate
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 1)) := by
  by_cases hk0 : k = 0
  · subst k
    have hpHi0 :
        0 <
          oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
      BinaryEndpointLevelVector_pos_of_not_first hold
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) (by
          simp [adjacentHighIndex, firstAdjacentIndex])
    have hpHi1 :
        oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤ 1 :=
      BinaryEndpointLevelVector_le_one hold
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
    have hrate :=
      lemmaC5_uniform_firstEndpointEqualSplit_rate_eq
        (le_of_lt hpHi0) hpHi1
    have hnot_last : (1 : ℕ) ≠ 2 * m + 1 := by omega
    have htwo_mod : 2 % (2 * m + 1 + 2) = 2 := by
      exact Nat.mod_eq_of_lt (by omega)
    simpa [binaryEndpointAwareAdjacentRate, uniformDoubledEndpointLevels,
      firstAdjacentIndex, adjacentHighIndex, hnot_last, hm.ne', htwo_mod] using
      hrate
  · by_cases hkm_eq : k = m
    · subst k
      have hpLo0 :
          0 ≤
            oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
        BinaryEndpointLevelVector_nonneg hold
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
      have hpLo1 :
          oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ 1 :=
        BinaryEndpointLevelVector_le_one hold
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
      have hrate :=
        lemmaC5_uniform_lastEndpointEqualSplit_rate_eq hpLo0 hpLo1
      have hnot_first : 2 * m + 1 ≠ 1 := by omega
      simpa [binaryEndpointAwareAdjacentRate, uniformDoubledEndpointLevels,
        lastAdjacentIndex, adjacentLowIndex, hnot_first, hm.ne'] using hrate
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkm : k < m := lt_of_le_of_ne hk hkm_eq
      have hpLo0 : 0 ≤ oldLevels (⟨k, by omega⟩ : Fin (m + 2)) :=
        BinaryEndpointLevelVector_nonneg hold ⟨k, by omega⟩
      have hpHi1 : oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) ≤ 1 :=
        BinaryEndpointLevelVector_le_one hold ⟨k + 1, by omega⟩
      have hlt : oldLevels (⟨k, by omega⟩ : Fin (m + 2)) <
          oldLevels (⟨k + 1, by omega⟩ : Fin (m + 2)) := by
        simpa [adjacentLowIndex, adjacentHighIndex] using
          hold.2.2 (⟨k, by omega⟩ : Fin (m + 1))
      have hrate :=
        lemmaC5_uniform_interiorEqualSplit_rate_eq hpLo0 hpHi1 hlt
      have hdiv : (2 * k + 1) / 2 = k := by
        rw [show 2 * k + 1 = 1 + 2 * k by omega]
        simp [Nat.add_mul_div_left]
      have hnot_first : 2 * k + 1 ≠ 1 := by omega
      have hnot_last : 2 * k + 1 ≠ 2 * m + 1 := by omega
      have hnot_even_last : 2 * k ≠ 2 * m + 1 := by omega
      have hnext_even : (2 * k + 1 + 1) % 2 = 0 := by omega
      have hnext_div : (2 * k + 1 + 1) / 2 = k + 1 := by
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
        simp
      simpa [binaryEndpointAwareAdjacentRate, uniformDoubledEndpointLevels,
        hdiv, hnot_first, hnot_last, hnot_even_last, hnext_even, hnext_div,
        hk0, hkm_eq] using hrate

/--
Every refined adjacent rate in the C.5 doubled chain is the C.5 transform of
the corresponding old adjacent rate, where the old index is `i / 2`.
-/
theorem uniformDoubledEndpointLevels_adjacent_rate_eq_transform
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (i : Fin ((2 * m + 1) + 1)) :
    binaryEndpointAwareAdjacentRate
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i =
      uniformDoubledEndpointRateTransform
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (⟨i.val / 2, by omega⟩ : Fin (m + 1))) := by
  let k : ℕ := i.val / 2
  have hk : k ≤ m := by
    have hi_lt : i.val < 2 * m + 2 := i.isLt
    omega
  by_cases hEven : i.val % 2 = 0
  · have hi_eq : i.val = 2 * k := by
      have hdecomp := Nat.mod_add_div i.val 2
      omega
    have hi_idx :
        i = (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 1)) := by
      ext
      exact hi_eq
    have hstep :=
      uniformDoubledEndpointLevels_even_adjacent_rate_eq_transform
        (m := m) (k := k) hm hk hold
    calc
      binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i =
        binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 1)) :=
          congrArg
            (fun idx =>
              binaryEndpointAwareAdjacentRate
                (uniformDoubledEndpointLevels oldLevels)
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) idx)
            hi_idx
      _ =
        uniformDoubledEndpointRateTransform
          (binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (⟨k, by omega⟩ : Fin (m + 1))) := hstep
      _ =
        uniformDoubledEndpointRateTransform
          (binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (⟨i.val / 2, by omega⟩ : Fin (m + 1))) := by
          rfl
  · have hOdd : i.val % 2 = 1 := by
      have hmod := Nat.mod_two_eq_zero_or_one i.val
      omega
    have hi_eq : i.val = 2 * k + 1 := by
      have hdecomp := Nat.mod_add_div i.val 2
      omega
    have hi_idx :
        i = (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 1)) := by
      ext
      exact hi_eq
    have hpair :=
      uniformDoubledEndpointLevels_adjacent_pair_rates_equal
        (m := m) (k := k) hm hk hold
    have hstep :=
      uniformDoubledEndpointLevels_even_adjacent_rate_eq_transform
        (m := m) (k := k) hm hk hold
    calc
      binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i =
        binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 1)) := by
          exact
            congrArg
              (fun idx =>
                binaryEndpointAwareAdjacentRate
                  (uniformDoubledEndpointLevels oldLevels)
                  (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) idx)
              hi_idx
      _ =
        binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 1)) := by
          simpa using hpair.symm
      _ =
        uniformDoubledEndpointRateTransform
          (binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (⟨i.val / 2, by omega⟩ : Fin (m + 1))) := by
          rw [hstep]

/--
Lemma C.5 global equalization certificate: if the old uniform endpoint chain
equalizes adjacent rates, then the explicit doubled chain also equalizes them.
-/
theorem uniformDoubledEndpointLevels_equalizes
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    BinaryEndpointAwareAdjacentRatesEqualize
      (uniformDoubledEndpointLevels oldLevels)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
  intro i j
  rw [uniformDoubledEndpointLevels_adjacent_rate_eq_transform hm hold i]
  rw [uniformDoubledEndpointLevels_adjacent_rate_eq_transform hm hold j]
  exact congrArg uniformDoubledEndpointRateTransform
    (holdEq (⟨i.val / 2, by omega⟩ : Fin (m + 1))
      (⟨j.val / 2, by omega⟩ : Fin (m + 1)))

/-- The one-interior-level endpoint vector `0, 1/2, 1`. -/
def binaryEndpointOneInteriorHalfLevel : Fin (1 + 2) → ℝ :=
  fun i => if i.val = 0 then 0 else if i.val = 1 then (1 / 2 : ℝ) else 1

/-- The vector `0, 1/2, 1` satisfies the endpoint level-vector convention. -/
theorem binaryEndpointOneInteriorHalfLevel_isEndpointLevelVector :
    BinaryEndpointLevelVector binaryEndpointOneInteriorHalfLevel := by
  constructor
  · simp [binaryEndpointOneInteriorHalfLevel]
  constructor
  · simp [binaryEndpointOneInteriorHalfLevel]
  · intro i
    fin_cases i <;>
      norm_num [binaryEndpointOneInteriorHalfLevel, adjacentLowIndex,
        adjacentHighIndex]

/--
For one interior level, the midpoint `1/2` equalizes the two endpoint-aware
adjacent rates.
-/
theorem binaryEndpointOneInteriorHalfLevel_equalizes
    (sampleRate : Fin (1 + 2) → ℝ) :
    BinaryEndpointAwareAdjacentRatesEqualize
      binaryEndpointOneInteriorHalfLevel sampleRate := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryEndpointOneInteriorHalfLevel,
      binaryEndpointAwareAdjacentRate, adjacentLowIndex, adjacentHighIndex]

/-- First endpoint level that realizes a positive endpoint-aware rate. -/
def binaryEndpointFirstLevelOfRate (g r : ℝ) : ℝ :=
  1 - Real.exp (-(r / g))

/-- Last interior level that realizes a positive endpoint-aware rate. -/
def binaryEndpointLastLevelOfRate (g r : ℝ) : ℝ :=
  Real.exp (-(r / g))

/-- The first endpoint inverse lies in the open unit interval for positive rate and weight. -/
theorem binaryEndpointFirstLevelOfRate_mem_Ioo
    {g r : ℝ} (hg : 0 < g) (hr : 0 < r) :
    binaryEndpointFirstLevelOfRate g r ∈ Set.Ioo (0 : ℝ) 1 := by
  have hdiv_pos : 0 < r / g := div_pos hr hg
  have hneg : -(r / g) < 0 := by linarith
  have hexp_lt_one : Real.exp (-(r / g)) < 1 :=
    Real.exp_lt_one_iff.mpr hneg
  have hexp_pos : 0 < Real.exp (-(r / g)) := Real.exp_pos _
  constructor <;> dsimp [binaryEndpointFirstLevelOfRate] <;> linarith

/-- The last endpoint inverse lies in the open unit interval for positive rate and weight. -/
theorem binaryEndpointLastLevelOfRate_mem_Ioo
    {g r : ℝ} (hg : 0 < g) (hr : 0 < r) :
    binaryEndpointLastLevelOfRate g r ∈ Set.Ioo (0 : ℝ) 1 := by
  have hdiv_pos : 0 < r / g := div_pos hr hg
  have hneg : -(r / g) < 0 := by linarith
  have hexp_lt_one : Real.exp (-(r / g)) < 1 :=
    Real.exp_lt_one_iff.mpr hneg
  exact ⟨Real.exp_pos _, hexp_lt_one⟩

/-- The first endpoint inverse realizes its target endpoint-aware rate. -/
theorem binaryEndpointFirstLevelOfRate_realizes
    {g r : ℝ} (hg : 0 < g) :
    g * (-Real.log (1 - binaryEndpointFirstLevelOfRate g r)) = r := by
  have hg_ne : g ≠ 0 := ne_of_gt hg
  rw [binaryEndpointFirstLevelOfRate]
  have hone_sub :
      1 - (1 - Real.exp (-(r / g))) = Real.exp (-(r / g)) := by
    ring
  rw [hone_sub, Real.log_exp]
  field_simp [hg_ne]

/-- The last endpoint inverse realizes its target endpoint-aware rate. -/
theorem binaryEndpointLastLevelOfRate_realizes
    {g r : ℝ} (hg : 0 < g) :
    g * (-Real.log (binaryEndpointLastLevelOfRate g r)) = r := by
  have hg_ne : g ≠ 0 := ne_of_gt hg
  rw [binaryEndpointLastLevelOfRate, Real.log_exp]
  field_simp [hg_ne]

/-- The first endpoint inverse is strictly increasing in the target rate. -/
theorem binaryEndpointFirstLevelOfRate_strictMono
    {g : ℝ} (hg : 0 < g) :
    StrictMono (binaryEndpointFirstLevelOfRate g) := by
  intro r s hrs
  have hdiv : r / g < s / g := by
    exact (div_lt_div_iff_of_pos_right hg).mpr hrs
  have hneg : -(s / g) < -(r / g) := by
    linarith
  have hexp : Real.exp (-(s / g)) < Real.exp (-(r / g)) :=
    Real.exp_lt_exp.mpr hneg
  dsimp [binaryEndpointFirstLevelOfRate]
  linarith

/-- The last endpoint inverse is strictly decreasing in the target rate. -/
theorem binaryEndpointLastLevelOfRate_strictAnti
    {g : ℝ} (hg : 0 < g) :
    StrictAnti (binaryEndpointLastLevelOfRate g) := by
  intro r s hrs
  have hdiv : r / g < s / g := by
    exact (div_lt_div_iff_of_pos_right hg).mpr hrs
  have hneg : -(s / g) < -(r / g) := by
    linarith
  dsimp [binaryEndpointLastLevelOfRate]
  exact Real.exp_lt_exp.mpr hneg

/-- The first endpoint inverse is continuous in the target rate. -/
theorem binaryEndpointFirstLevelOfRate_continuous (g : ℝ) :
    Continuous (binaryEndpointFirstLevelOfRate g) := by
  unfold binaryEndpointFirstLevelOfRate
  fun_prop

/-- The last endpoint inverse is continuous in the target rate. -/
theorem binaryEndpointLastLevelOfRate_continuous (g : ℝ) :
    Continuous (binaryEndpointLastLevelOfRate g) := by
  unfold binaryEndpointLastLevelOfRate
  fun_prop

/-- The first endpoint inverse tends to the upper endpoint as the target rate grows. -/
theorem binaryEndpointFirstLevelOfRate_tendsto_atTop
    {g : ℝ} (hg : 0 < g) :
    Filter.Tendsto (binaryEndpointFirstLevelOfRate g)
      Filter.atTop (nhds 1) := by
  have hg_ne : g ≠ 0 := ne_of_gt hg
  have hcoef : -(1 / g) < 0 := by
    have hpos : 0 < (1 / g : ℝ) := one_div_pos.mpr hg
    linarith
  have hlin :
      Filter.Tendsto (fun r : ℝ => -(r / g))
        Filter.atTop Filter.atBot := by
    have hmul :
        Filter.Tendsto (fun r : ℝ => (-(1 / g)) * r + 0)
          Filter.atTop Filter.atBot :=
      (Filter.Tendsto.const_mul_atTop_of_neg hcoef Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hmul using 1
    ext r
    field_simp [hg_ne]
    ring
  have hexp :
      Filter.Tendsto (fun r : ℝ => Real.exp (-(r / g)))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa [binaryEndpointFirstLevelOfRate] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hexp

/-- The last endpoint inverse tends to the lower endpoint as the target rate grows. -/
theorem binaryEndpointLastLevelOfRate_tendsto_atTop
    {g : ℝ} (hg : 0 < g) :
    Filter.Tendsto (binaryEndpointLastLevelOfRate g)
      Filter.atTop (nhds 0) := by
  have hg_ne : g ≠ 0 := ne_of_gt hg
  have hcoef : -(1 / g) < 0 := by
    have hpos : 0 < (1 / g : ℝ) := one_div_pos.mpr hg
    linarith
  have hlin :
      Filter.Tendsto (fun r : ℝ => -(r / g))
        Filter.atTop Filter.atBot := by
    have hmul :
        Filter.Tendsto (fun r : ℝ => (-(1 / g)) * r + 0)
          Filter.atTop Filter.atBot :=
      (Filter.Tendsto.const_mul_atTop_of_neg hcoef Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hmul using 1
    ext r
    field_simp [hg_ne]
    ring
  simpa [binaryEndpointLastLevelOfRate] using
    Real.tendsto_exp_atBot.comp hlin

/-- The first endpoint rate is strictly increasing in the endpoint level. -/
theorem binaryEndpointFirstRate_strictMonoOn
    {g : ℝ} (hg : 0 < g) :
    StrictMonoOn (fun p : ℝ => g * (-Real.log (1 - p))) (Set.Iio 1) := by
  intro p hp q hq hpq
  have hsub_pos_q : 0 < 1 - q := sub_pos.mpr hq
  have hsub_lt : 1 - q < 1 - p := by linarith
  have hlog : Real.log (1 - q) < Real.log (1 - p) :=
    Real.log_lt_log hsub_pos_q hsub_lt
  have hneg : -Real.log (1 - p) < -Real.log (1 - q) := by
    linarith
  exact mul_lt_mul_of_pos_left hneg hg

/--
Comparison form of the first endpoint inverse: its selected level lies below
`p` exactly when the target rate lies below the endpoint rate at `p`.
-/
theorem binaryEndpointFirstLevelOfRate_lt_iff
    {g r p : ℝ} (hg : 0 < g) (hp : p < 1) :
    binaryEndpointFirstLevelOfRate g r < p ↔
      r < g * (-Real.log (1 - p)) := by
  let rate : ℝ → ℝ := fun x => g * (-Real.log (1 - x))
  have hroot_mem : binaryEndpointFirstLevelOfRate g r ∈ Set.Iio (1 : ℝ) := by
    dsimp [binaryEndpointFirstLevelOfRate]
    exact sub_lt_self 1 (Real.exp_pos _)
  have hp_mem : p ∈ Set.Iio (1 : ℝ) := hp
  have hroot_rate : rate (binaryEndpointFirstLevelOfRate g r) = r :=
    binaryEndpointFirstLevelOfRate_realizes hg
  have hmono := binaryEndpointFirstRate_strictMonoOn hg
  constructor
  · intro hlt
    simpa [rate, hroot_rate] using hmono hroot_mem hp_mem hlt
  · intro hrate
    by_contra hnot
    have hp_le_root : p ≤ binaryEndpointFirstLevelOfRate g r :=
      le_of_not_gt hnot
    rcases lt_or_eq_of_le hp_le_root with hlt | heq
    · have hlt_rate :
          rate p < rate (binaryEndpointFirstLevelOfRate g r) :=
        hmono hp_mem hroot_mem hlt
      linarith
    · subst p
      linarith

/-- The last endpoint rate is strictly decreasing in the endpoint level. -/
theorem binaryEndpointLastRate_strictAntiOn
    {g : ℝ} (hg : 0 < g) :
    StrictAntiOn (fun p : ℝ => g * (-Real.log p)) (Set.Ioi 0) := by
  intro p hp q hq hpq
  have hlog : Real.log p < Real.log q :=
    Real.log_lt_log hp hpq
  have hneg : -Real.log q < -Real.log p := by
    linarith
  exact mul_lt_mul_of_pos_left hneg hg

/--
Comparison form of the last endpoint inverse: `p` lies below its selected
level exactly when the target rate lies below the endpoint rate at `p`.
-/
theorem lt_binaryEndpointLastLevelOfRate_iff
    {g r p : ℝ} (hg : 0 < g) (hp : 0 < p) :
    p < binaryEndpointLastLevelOfRate g r ↔
      r < g * (-Real.log p) := by
  let rate : ℝ → ℝ := fun x => g * (-Real.log x)
  have hroot_mem : binaryEndpointLastLevelOfRate g r ∈ Set.Ioi (0 : ℝ) := by
    dsimp [binaryEndpointLastLevelOfRate]
    exact Real.exp_pos _
  have hp_mem : p ∈ Set.Ioi (0 : ℝ) := hp
  have hroot_rate : rate (binaryEndpointLastLevelOfRate g r) = r :=
    binaryEndpointLastLevelOfRate_realizes hg
  have hanti := binaryEndpointLastRate_strictAntiOn hg
  constructor
  · intro hlt
    simpa [rate, hroot_rate] using hanti hp_mem hroot_mem hlt
  · intro hrate
    by_contra hnot
    have hroot_le_p : binaryEndpointLastLevelOfRate g r ≤ p :=
      le_of_not_gt hnot
    rcases lt_or_eq_of_le hroot_le_p with hlt | heq
    · have hlt_rate :
          rate p < rate (binaryEndpointLastLevelOfRate g r) :=
        hanti hroot_mem hp_mem hlt
      linarith
    · subst p
      linarith

/--
The middle closed rate induced by the two endpoint inverse levels for a
two-interior-level chain.
-/
def binaryEndpointTwoInteriorMiddleRate (gLo gHi r : ℝ) : ℝ :=
  weightedBernoulliClosedThresholdRate gHi gLo
    (binaryEndpointLastLevelOfRate gHi r)
    (binaryEndpointFirstLevelOfRate gLo r)

/--
Scalar gap whose zero is the target-rate equation for the two-interior-level
endpoint-aware equalization problem.
-/
def binaryEndpointTwoInteriorMiddleRateGap (gLo gHi r : ℝ) : ℝ :=
  binaryEndpointTwoInteriorMiddleRate gLo gHi r - r

/--
The two-interior-level middle-rate function is continuous at every positive
target rate.
-/
theorem binaryEndpointTwoInteriorMiddleRate_continuousAt
    {gLo gHi r : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hr : 0 < r) :
    ContinuousAt (binaryEndpointTwoInteriorMiddleRate gLo gHi) r := by
  let pHi : ℝ := binaryEndpointLastLevelOfRate gHi r
  let pLo : ℝ := binaryEndpointFirstLevelOfRate gLo r
  have hpHi_mem : pHi ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [pHi]
    exact binaryEndpointLastLevelOfRate_mem_Ioo hgHi hr
  have hpLo_mem : pLo ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [pLo]
    exact binaryEndpointFirstLevelOfRate_mem_Ioo hgLo hr
  have hclosed :
      ContinuousAt
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
        (pHi, pLo) :=
    weightedBernoulliClosedThresholdRate_continuousAt_pair
      hpHi_mem.1 hpHi_mem.2 hpLo_mem.1 hpLo_mem.2
  have hpair :
      ContinuousAt
        (fun s : ℝ =>
          (binaryEndpointLastLevelOfRate gHi s,
            binaryEndpointFirstLevelOfRate gLo s))
        r :=
    (binaryEndpointLastLevelOfRate_continuous gHi).continuousAt.prodMk
      (binaryEndpointFirstLevelOfRate_continuous gLo).continuousAt
  simpa [binaryEndpointTwoInteriorMiddleRate, pHi, pLo] using
    hclosed.comp_of_eq hpair (by rfl)

/-- The two-interior-level scalar target-rate gap is continuous at positive rates. -/
theorem binaryEndpointTwoInteriorMiddleRateGap_continuousAt
    {gLo gHi r : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hr : 0 < r) :
    ContinuousAt (binaryEndpointTwoInteriorMiddleRateGap gLo gHi) r := by
  simpa [binaryEndpointTwoInteriorMiddleRateGap] using
    (binaryEndpointTwoInteriorMiddleRate_continuousAt
      hgLo hgHi hr).sub continuousAt_id

/--
The two-interior scalar target-rate gap is continuous on the positive-rate
domain.
-/
theorem binaryEndpointTwoInteriorMiddleRateGap_continuousOn_Ioi
    {gLo gHi : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) :
    ContinuousOn (binaryEndpointTwoInteriorMiddleRateGap gLo gHi)
      (Set.Ioi (0 : ℝ)) := by
  intro r hr
  exact
    (binaryEndpointTwoInteriorMiddleRateGap_continuousAt
      hgLo hgHi hr).continuousWithinAt

/--
Along the two-interior endpoint-inverse path, the closed-rate base tends to
zero from the positive side as the target rate approaches zero from above.
-/
theorem binaryEndpointTwoInteriorMiddleRateBase_tendsto_nhdsGT_zero
    {gLo gHi : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) :
    Filter.Tendsto
      (fun r : ℝ =>
        weightedBernoulliClosedRateBase gHi gLo
          (binaryEndpointLastLevelOfRate gHi r)
          (binaryEndpointFirstLevelOfRate gLo r))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  let aLo : ℝ := gLo / (gHi + gLo)
  let aHi : ℝ := gHi / (gHi + gLo)
  have hG_pos : 0 < gHi + gLo := add_pos hgHi hgLo
  have haLo_nonneg : 0 ≤ aLo := by
    dsimp [aLo]
    exact div_nonneg hgLo.le hG_pos.le
  have haHi_nonneg : 0 ≤ aHi := by
    dsimp [aHi]
    exact div_nonneg hgHi.le hG_pos.le
  have haLo_pos : 0 < aLo := by
    dsimp [aLo]
    exact div_pos hgLo hG_pos
  have haHi_pos : 0 < aHi := by
    dsimp [aHi]
    exact div_pos hgHi hG_pos
  have hfirst :
      Filter.Tendsto (binaryEndpointFirstLevelOfRate gLo)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    by
      have hcont :
          ContinuousAt (binaryEndpointFirstLevelOfRate gLo) (0 : ℝ) :=
        (binaryEndpointFirstLevelOfRate_continuous gLo).continuousAt
      simpa [binaryEndpointFirstLevelOfRate] using
        hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlast :
      Filter.Tendsto (binaryEndpointLastLevelOfRate gHi)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) :=
    by
      have hcont :
          ContinuousAt (binaryEndpointLastLevelOfRate gHi) (0 : ℝ) :=
        (binaryEndpointLastLevelOfRate_continuous gHi).continuousAt
      simpa [binaryEndpointLastLevelOfRate] using
        hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hfailLo :
      Filter.Tendsto
        (fun r : ℝ => (1 - binaryEndpointFirstLevelOfRate gLo r) ^ aLo)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hsub :
        Filter.Tendsto
          (fun r : ℝ => 1 - binaryEndpointFirstLevelOfRate gLo r)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hfirst
    simpa using hsub.rpow_const (p := aLo) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hfailHi :
      Filter.Tendsto
        (fun r : ℝ => (1 - binaryEndpointLastLevelOfRate gHi r) ^ aHi)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hsub :
        Filter.Tendsto
          (fun r : ℝ => 1 - binaryEndpointLastLevelOfRate gHi r)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlast
    simpa [Real.zero_rpow haHi_pos.ne'] using
      hsub.rpow_const (p := aHi) (Or.inr haHi_nonneg)
  have hsuccLo :
      Filter.Tendsto
        (fun r : ℝ => (binaryEndpointFirstLevelOfRate gLo r) ^ aLo)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.zero_rpow haLo_pos.ne'] using
      hfirst.rpow_const (p := aLo) (Or.inr haLo_nonneg)
  have hsuccHi :
      Filter.Tendsto
        (fun r : ℝ => (binaryEndpointLastLevelOfRate gHi r) ^ aHi)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    simpa using hlast.rpow_const (p := aHi) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hbase_nhds :
      Filter.Tendsto
        (fun r : ℝ =>
          weightedBernoulliClosedRateBase gHi gLo
            (binaryEndpointLastLevelOfRate gHi r)
            (binaryEndpointFirstLevelOfRate gLo r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [weightedBernoulliClosedRateBase,
      weightedBernoulliFailureBase, weightedBernoulliSuccessBase, aLo, aHi,
      add_comm, add_left_comm, add_assoc] using
      (hfailLo.mul hfailHi).add (hsuccLo.mul hsuccHi)
  have hbase_pos :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        weightedBernoulliClosedRateBase gHi gLo
          (binaryEndpointLastLevelOfRate gHi r)
          (binaryEndpointFirstLevelOfRate gLo r) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    have hpHi_mem :
        binaryEndpointLastLevelOfRate gHi r ∈ Set.Ioo (0 : ℝ) 1 :=
      binaryEndpointLastLevelOfRate_mem_Ioo hgHi hr
    have hpLo_mem :
        binaryEndpointFirstLevelOfRate gLo r ∈ Set.Ioo (0 : ℝ) 1 :=
      binaryEndpointFirstLevelOfRate_mem_Ioo hgLo hr
    exact
      weightedBernoulliClosedRateBase_pos
        hpHi_mem.1 hpHi_mem.2 hpLo_mem.1 hpLo_mem.2
  exact
    tendsto_nhdsWithin_iff.mpr ⟨hbase_nhds, hbase_pos⟩

/--
The two-interior middle closed rate diverges as the target rate approaches
zero from above.
-/
theorem binaryEndpointTwoInteriorMiddleRate_tendsto_nhdsGT_zero_atTop
    {gLo gHi : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) :
    Filter.Tendsto (binaryEndpointTwoInteriorMiddleRate gLo gHi)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
  have hG_pos : 0 < gHi + gLo := add_pos hgHi hgLo
  have hbase :=
    binaryEndpointTwoInteriorMiddleRateBase_tendsto_nhdsGT_zero
      hgLo hgHi
  have hlog :
      Filter.Tendsto
        (fun r : ℝ =>
          Real.log
            (weightedBernoulliClosedRateBase gHi gLo
              (binaryEndpointLastLevelOfRate gHi r)
              (binaryEndpointFirstLevelOfRate gLo r)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hbase
  have hneglog :
      Filter.Tendsto
        (fun r : ℝ =>
          -Real.log
            (weightedBernoulliClosedRateBase gHi gLo
              (binaryEndpointLastLevelOfRate gHi r)
              (binaryEndpointFirstLevelOfRate gLo r)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hlog
  have hscaled :
      Filter.Tendsto
        (fun r : ℝ =>
          (gHi + gLo) *
            (-Real.log
              (weightedBernoulliClosedRateBase gHi gLo
                (binaryEndpointLastLevelOfRate gHi r)
                (binaryEndpointFirstLevelOfRate gLo r))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
    hneglog.const_mul_atTop hG_pos
  convert hscaled using 1
  ext r
  simp [binaryEndpointTwoInteriorMiddleRate,
    weightedBernoulliClosedThresholdRate]
  ring

/--
The two-interior scalar target-rate gap is eventually positive near target
rate zero.
-/
theorem binaryEndpointTwoInteriorMiddleRateGap_eventually_pos_nhdsGT_zero
    {gLo gHi : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) :
    ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < binaryEndpointTwoInteriorMiddleRateGap gLo gHi r := by
  have hrate :=
    binaryEndpointTwoInteriorMiddleRate_tendsto_nhdsGT_zero_atTop
      hgLo hgHi
  have hrate_gt_one :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        1 < binaryEndpointTwoInteriorMiddleRate gLo gHi r :=
    hrate.eventually_gt_atTop (1 : ℝ)
  have hid :
      Filter.Tendsto (fun r : ℝ => r)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hr_lt_one :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < 1 :=
    hid.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hrate_gt_one, hr_lt_one] with r hrate_one hr_one
  dsimp [binaryEndpointTwoInteriorMiddleRateGap]
  linarith

/-- There is a positive target rate where the two-interior scalar gap is positive. -/
theorem binaryEndpointTwoInteriorMiddleRateGap_exists_pos
    {gLo gHi : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) :
    ∃ r : ℝ, 0 < r ∧
      0 < binaryEndpointTwoInteriorMiddleRateGap gLo gHi r := by
  have hev :=
    binaryEndpointTwoInteriorMiddleRateGap_eventually_pos_nhdsGT_zero
      hgLo hgHi
  have hpos :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r :=
    self_mem_nhdsWithin
  exact (hpos.and hev).exists

/--
Endpoint inverse gap for the scalar shooting interval: negative means the
first endpoint inverse lies below the last endpoint inverse.
-/
def binaryEndpointInverseGap (gFirst gLast r : ℝ) : ℝ :=
  binaryEndpointFirstLevelOfRate gFirst r -
    binaryEndpointLastLevelOfRate gLast r

/-- The endpoint inverse gap is continuous in the target rate. -/
theorem binaryEndpointInverseGap_continuous (gFirst gLast : ℝ) :
    Continuous (binaryEndpointInverseGap gFirst gLast) := by
  unfold binaryEndpointInverseGap
  exact
    (binaryEndpointFirstLevelOfRate_continuous gFirst).sub
      (binaryEndpointLastLevelOfRate_continuous gLast)

/-- The endpoint inverse gap is strictly increasing in the target rate. -/
theorem binaryEndpointInverseGap_strictMono
    {gFirst gLast : ℝ} (hgFirst : 0 < gFirst) (hgLast : 0 < gLast) :
    StrictMono (binaryEndpointInverseGap gFirst gLast) := by
  intro r s hrs
  have hfirst :
      binaryEndpointFirstLevelOfRate gFirst r <
        binaryEndpointFirstLevelOfRate gFirst s :=
    binaryEndpointFirstLevelOfRate_strictMono hgFirst hrs
  have hlast :
      binaryEndpointLastLevelOfRate gLast s <
        binaryEndpointLastLevelOfRate gLast r :=
    binaryEndpointLastLevelOfRate_strictAnti hgLast hrs
  unfold binaryEndpointInverseGap
  linarith

@[simp] theorem binaryEndpointFirstLevelOfRate_zero (g : ℝ) :
    binaryEndpointFirstLevelOfRate g 0 = 0 := by
  simp [binaryEndpointFirstLevelOfRate]

@[simp] theorem binaryEndpointLastLevelOfRate_zero (g : ℝ) :
    binaryEndpointLastLevelOfRate g 0 = 1 := by
  simp [binaryEndpointLastLevelOfRate]

@[simp] theorem binaryEndpointInverseGap_zero (gFirst gLast : ℝ) :
    binaryEndpointInverseGap gFirst gLast 0 = -1 := by
  simp [binaryEndpointInverseGap]

/-- The endpoint inverse gap tends to one as the target rate grows. -/
theorem binaryEndpointInverseGap_tendsto_atTop
    {gFirst gLast : ℝ} (hgFirst : 0 < gFirst) (hgLast : 0 < gLast) :
    Filter.Tendsto (binaryEndpointInverseGap gFirst gLast)
      Filter.atTop (nhds 1) := by
  have hfirst :=
    binaryEndpointFirstLevelOfRate_tendsto_atTop (g := gFirst) hgFirst
  have hlast :=
    binaryEndpointLastLevelOfRate_tendsto_atTop (g := gLast) hgLast
  simpa [binaryEndpointInverseGap] using hfirst.sub hlast

/-- The endpoint inverse gap is positive somewhere for positive endpoint weights. -/
theorem binaryEndpointInverseGap_exists_pos
    {gFirst gLast : ℝ} (hgFirst : 0 < gFirst) (hgLast : 0 < gLast) :
    ∃ r : ℝ, 0 < binaryEndpointInverseGap gFirst gLast r := by
  have hlim :=
    binaryEndpointInverseGap_tendsto_atTop hgFirst hgLast
  have hev :
      ∀ᶠ r in Filter.atTop, 0 < binaryEndpointInverseGap gFirst gLast r :=
    hlim.eventually (eventually_gt_nhds zero_lt_one)
  exact hev.exists

/--
Unique endpoint-inverse crossing. The crossing is the upper boundary of target
rates for which the first endpoint inverse remains below the last endpoint
inverse.
-/
theorem binaryEndpointInverseGap_existsUnique_zero_and_nonneg_iff
    {gFirst gLast : ℝ} (hgFirst : 0 < gFirst) (hgLast : 0 < gLast) :
    ∃! r : ℝ,
      binaryEndpointInverseGap gFirst gLast r = 0 ∧
        ∀ z : ℝ, 0 ≤ binaryEndpointInverseGap gFirst gLast z ↔ r ≤ z := by
  have hneg : ∃ r : ℝ, binaryEndpointInverseGap gFirst gLast r < 0 := by
    refine ⟨0, ?_⟩
    simp
  exact
    AppliedModelingLib.existsUnique_zero_and_nonneg_iff_of_continuous_strictMono_crossing
      (binaryEndpointInverseGap_continuous gFirst gLast)
      (binaryEndpointInverseGap_strictMono hgFirst hgLast)
      hneg (binaryEndpointInverseGap_exists_pos hgFirst hgLast)

/--
The endpoint inverse crossing is positive. This is the scalar interval upper
endpoint for the forward-shooting proof of finite Lemma 3.1.
-/
theorem binaryEndpointInverseGap_existsUnique_pos_zero_and_nonneg_iff
    {gFirst gLast : ℝ} (hgFirst : 0 < gFirst) (hgLast : 0 < gLast) :
    ∃! r : ℝ,
      0 < r ∧ binaryEndpointInverseGap gFirst gLast r = 0 ∧
        ∀ z : ℝ, 0 ≤ binaryEndpointInverseGap gFirst gLast z ↔ r ≤ z := by
  rcases
    binaryEndpointInverseGap_existsUnique_zero_and_nonneg_iff
      hgFirst hgLast with
    ⟨r, hr, huniq⟩
  have hrpos : 0 < r := by
    have hnot_nonneg :
        ¬ 0 ≤ binaryEndpointInverseGap gFirst gLast 0 := by
      simp
    have hnot_le : ¬ r ≤ 0 := by
      intro hle
      exact hnot_nonneg ((hr.2 0).mpr hle)
    exact lt_of_not_ge hnot_le
  refine ⟨r, ⟨hrpos, hr.1, hr.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.2.1, hy.2.2⟩

/--
Below the endpoint inverse crossing, the lower endpoint inverse is strictly
below the upper endpoint inverse.
-/
theorem binaryEndpointFirstLevelOfRate_lt_lastLevelOfRate_of_lt_inverseGap_crossing
    {gFirst gLast crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap gFirst gLast crossing = 0 ∧
        ∀ z : ℝ, 0 ≤ binaryEndpointInverseGap gFirst gLast z ↔
          crossing ≤ z)
    (hr : r < crossing) :
    binaryEndpointFirstLevelOfRate gFirst r <
      binaryEndpointLastLevelOfRate gLast r := by
  have hnot_nonneg :
      ¬ 0 ≤ binaryEndpointInverseGap gFirst gLast r := by
    intro hnonneg
    exact (not_le_of_gt hr) ((hcross.2 r).mp hnonneg)
  have hneg : binaryEndpointInverseGap gFirst gLast r < 0 :=
    lt_of_not_ge hnot_nonneg
  unfold binaryEndpointInverseGap at hneg
  linarith

/--
At or above the endpoint inverse crossing, the upper endpoint inverse is no
larger than the lower endpoint inverse.
-/
theorem binaryEndpointLastLevelOfRate_le_firstLevelOfRate_of_inverseGap_crossing_le
    {gFirst gLast crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap gFirst gLast crossing = 0 ∧
        ∀ z : ℝ, 0 ≤ binaryEndpointInverseGap gFirst gLast z ↔
          crossing ≤ z)
    (hr : crossing ≤ r) :
    binaryEndpointLastLevelOfRate gLast r ≤
      binaryEndpointFirstLevelOfRate gFirst r := by
  have hnonneg : 0 ≤ binaryEndpointInverseGap gFirst gLast r :=
    (hcross.2 r).mpr hr
  unfold binaryEndpointInverseGap at hnonneg
  linarith

/--
At the endpoint-inverse crossing, the two-interior middle rate collapses to
the diagonal closed rate, so the scalar target-rate gap is `-crossing`.
-/
theorem binaryEndpointTwoInteriorMiddleRateGap_eq_neg_at_inverseGap_crossing
    {gLo gHi crossing : ℝ}
    (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hcrossing : 0 < crossing)
    (hcross : binaryEndpointInverseGap gLo gHi crossing = 0) :
    binaryEndpointTwoInteriorMiddleRateGap gLo gHi crossing =
      -crossing := by
  have hlevels_eq :
      binaryEndpointFirstLevelOfRate gLo crossing =
        binaryEndpointLastLevelOfRate gHi crossing := by
    unfold binaryEndpointInverseGap at hcross
    linarith
  have hpLast_mem :
      binaryEndpointLastLevelOfRate gHi crossing ∈ Set.Ioo (0 : ℝ) 1 :=
    binaryEndpointLastLevelOfRate_mem_Ioo hgHi hcrossing
  simp [binaryEndpointTwoInteriorMiddleRateGap,
    binaryEndpointTwoInteriorMiddleRate, hlevels_eq,
    weightedBernoulliClosedThresholdRate_self hgHi hgLo
      hpLast_mem.1 hpLast_mem.2]

/-- The two-interior scalar gap is negative at the endpoint-inverse crossing. -/
theorem binaryEndpointTwoInteriorMiddleRateGap_neg_at_inverseGap_crossing
    {gLo gHi crossing : ℝ}
    (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hcrossing : 0 < crossing)
    (hcross : binaryEndpointInverseGap gLo gHi crossing = 0) :
    binaryEndpointTwoInteriorMiddleRateGap gLo gHi crossing < 0 := by
  rw [
    binaryEndpointTwoInteriorMiddleRateGap_eq_neg_at_inverseGap_crossing
      hgLo hgHi hcrossing hcross]
  linarith

/--
The two-interior scalar target-rate equation has a positive root before the
endpoint-inverse crossing.
-/
theorem binaryEndpointTwoInteriorMiddleRateGap_exists_zero
    {gLo gHi : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) :
    ∃ r : ℝ,
      0 < r ∧
        binaryEndpointFirstLevelOfRate gLo r <
          binaryEndpointLastLevelOfRate gHi r ∧
        binaryEndpointTwoInteriorMiddleRateGap gLo gHi r = 0 := by
  rcases
    binaryEndpointInverseGap_existsUnique_pos_zero_and_nonneg_iff
      hgLo hgHi with
    ⟨crossing, hcrossing, _hcrossing_unique⟩
  have hgap_neg :
      binaryEndpointTwoInteriorMiddleRateGap gLo gHi crossing < 0 :=
    binaryEndpointTwoInteriorMiddleRateGap_neg_at_inverseGap_crossing
      hgLo hgHi hcrossing.1 hcrossing.2.1
  have hev_gap_pos :=
    binaryEndpointTwoInteriorMiddleRateGap_eventually_pos_nhdsGT_zero
      hgLo hgHi
  have hev_r_pos :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r :=
    self_mem_nhdsWithin
  have hid :
      Filter.Tendsto (fun r : ℝ => r)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hev_lt_crossing :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < crossing :=
    hid.eventually (eventually_lt_nhds hcrossing.1)
  rcases (hev_r_pos.and (hev_gap_pos.and hev_lt_crossing)).exists with
    ⟨left, hleft_pos, hgap_left_pos, hleft_lt_crossing⟩
  let gap : ℝ → ℝ := binaryEndpointTwoInteriorMiddleRateGap gLo gHi
  have hcont : ContinuousOn gap (Set.Icc left crossing) := by
    exact
      (binaryEndpointTwoInteriorMiddleRateGap_continuousOn_Ioi
        hgLo hgHi).mono (by
          intro x hx
          exact hleft_pos.trans_le hx.1)
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (gap crossing) (gap left) := by
    constructor <;> dsimp [gap] <;> linarith
  rcases intermediate_value_Icc'
      (le_of_lt hleft_lt_crossing) hcont hzero_mem with
    ⟨root, hroot_mem, hroot_gap⟩
  have hroot_pos : 0 < root := hleft_pos.trans_le hroot_mem.1
  have hroot_lt_crossing : root < crossing := by
    have hne : root ≠ crossing := by
      intro h
      subst root
      dsimp [gap] at hroot_gap
      linarith
    exact lt_of_le_of_ne hroot_mem.2 hne
  have horder :
      binaryEndpointFirstLevelOfRate gLo root <
        binaryEndpointLastLevelOfRate gHi root :=
    binaryEndpointFirstLevelOfRate_lt_lastLevelOfRate_of_lt_inverseGap_crossing
      ⟨hcrossing.2.1, hcrossing.2.2⟩ hroot_lt_crossing
  exact ⟨root, hroot_pos, horder, hroot_gap⟩

/-- Natural-number view of a finite endpoint-chain sample-rate vector. -/
def binaryEndpointSampleRateNat {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (n : ℕ) : ℝ :=
  if h : n < m + 2 then sampleRate ⟨n, h⟩ else 0

/--
Forward clipped cascade for the finite endpoint-aware equalization problem.
The recursion starts from the lower endpoint and the first endpoint inverse,
then repeatedly shoots for the next high endpoint unless the requested target
rate is no longer attainable before the supplied cap.
-/
def binaryEndpointForwardClippedLevelNat {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 =>
      binaryEndpointFirstLevelOfRate
        (binaryEndpointSampleRateNat sampleRate 1) r
  | n + 2 =>
      weightedBernoulliHighEndpointOfRateOrCap
        (binaryEndpointSampleRateNat sampleRate (n + 2))
        (binaryEndpointSampleRateNat sampleRate (n + 1))
        (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1))
        cap r

/--
If the first forward-clipped level is already at the cap, every later recursive
level remains at the cap.
-/
theorem binaryEndpointForwardClippedLevelNat_eq_cap_of_first_eq_cap {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ)
    (hfirst :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r =
        cap) :
    ∀ n : ℕ, 1 ≤ n →
      binaryEndpointForwardClippedLevelNat sampleRate cap r n = cap := by
  intro n hn
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          simpa [binaryEndpointForwardClippedLevelNat] using hfirst
      | succ n =>
          change
            weightedBernoulliHighEndpointOfRateOrCap
                (binaryEndpointSampleRateNat sampleRate (n + 2))
                (binaryEndpointSampleRateNat sampleRate (n + 1))
                (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1))
                cap r =
              cap
          rw [ih (by omega)]
          exact
            weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_lt_cap
              (lt_irrefl cap)

/--
Once a positive-index forward-clipped level reaches the cap, every later level
remains at the cap.
-/
theorem binaryEndpointForwardClippedLevelNat_eq_cap_of_eq_cap {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ) {k : ℕ}
    (hk_pos : 1 ≤ k)
    (hk :
      binaryEndpointForwardClippedLevelNat sampleRate cap r k = cap) :
    ∀ n : ℕ, k ≤ n →
      binaryEndpointForwardClippedLevelNat sampleRate cap r n = cap := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base =>
      exact hk
  | succ n hkn ih =>
      cases n with
      | zero =>
          omega
      | succ n =>
          change
            weightedBernoulliHighEndpointOfRateOrCap
                (binaryEndpointSampleRateNat sampleRate (n + 2))
                (binaryEndpointSampleRateNat sampleRate (n + 1))
                (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1))
                cap r =
              cap
          rw [ih]
          exact
            weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_lt_cap
              (lt_irrefl cap)

/--
If the first positive forward-clipped level lies below the cap, then every later
positive-index level also lies below the cap.
-/
theorem binaryEndpointForwardClippedLevelNat_le_cap_of_first_le_cap {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ)
    (hfirst :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r ≤
        cap) :
    ∀ n : ℕ, 1 ≤ n →
      binaryEndpointForwardClippedLevelNat sampleRate cap r n ≤ cap := by
  intro n hn
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          simpa [binaryEndpointForwardClippedLevelNat] using hfirst
      | succ n =>
          change
            weightedBernoulliHighEndpointOfRateOrCap
                (binaryEndpointSampleRateNat sampleRate (n + 2))
                (binaryEndpointSampleRateNat sampleRate (n + 1))
                (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1))
                cap r ≤
              cap
          exact
            weightedBernoulliHighEndpointOfRateOrCap_le_cap
              (ih (by omega))

/--
If the first positive forward-clipped level is positive and lies below the cap,
then every positive-index recursive level is positive.
-/
theorem binaryEndpointForwardClippedLevelNat_pos_of_first_pos_le_cap {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ)
    (hfirst_pos :
      0 <
        binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r)
    (hfirst_le :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r ≤
        cap) :
    ∀ n : ℕ, 1 ≤ n →
      0 < binaryEndpointForwardClippedLevelNat sampleRate cap r n := by
  intro n hn
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          simpa [binaryEndpointForwardClippedLevelNat] using hfirst_pos
      | succ n =>
          have hprev_le :
              binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1) ≤
                cap :=
            binaryEndpointForwardClippedLevelNat_le_cap_of_first_le_cap
              sampleRate cap r hfirst_le (n + 1) (by omega)
          have hprev_pos :
              0 <
                binaryEndpointForwardClippedLevelNat sampleRate cap r
                  (n + 1) :=
            ih (by omega)
          change
            0 <
              weightedBernoulliHighEndpointOfRateOrCap
                (binaryEndpointSampleRateNat sampleRate (n + 2))
                (binaryEndpointSampleRateNat sampleRate (n + 1))
                (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1))
                cap r
          exact
            hprev_pos.trans_le
              (le_weightedBernoulliHighEndpointOfRateOrCap hprev_le)

/--
Finite endpoint vector from the forward clipped cascade and the last endpoint
inverse cap.
-/
def binaryEndpointForwardClippedLevels {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) : Fin (m + 2) → ℝ :=
  let cap : ℝ :=
    binaryEndpointLastLevelOfRate
      (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) r
  fun i =>
    if i.val = 0 then 0
    else if i.val = m + 1 then 1
    else if i.val = m then cap
    else binaryEndpointForwardClippedLevelNat sampleRate cap r i.val

/-- Last endpoint-inverse cap used by the forward clipped cascade. -/
def binaryEndpointForwardClippedCap {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) : ℝ :=
  binaryEndpointLastLevelOfRate
    (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) r

/-- The last endpoint-inverse cap used by the forward cascade is continuous. -/
theorem binaryEndpointForwardClippedCap_continuous {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) :
    Continuous (binaryEndpointForwardClippedCap sampleRate) := by
  unfold binaryEndpointForwardClippedCap
  exact binaryEndpointLastLevelOfRate_continuous
    (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))

/--
Below the endpoint-inverse crossing, the first forward-clipped level is no larger
than the last endpoint-inverse cap.
-/
theorem binaryEndpointForwardClippedFirst_le_cap_of_le_inverseGap_crossing
    {m : ℕ} (sampleRate : Fin (m + 2) → ℝ)
    (hgFirst : 0 < binaryEndpointSampleRateNat sampleRate 1)
    (hgLast : 0 < binaryEndpointSampleRateNat sampleRate m)
    {crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (hr_le_crossing : r ≤ crossing) :
    binaryEndpointFirstLevelOfRate
        (binaryEndpointSampleRateNat sampleRate 1) r ≤
      binaryEndpointForwardClippedCap sampleRate r := by
  have hgap_le :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) r ≤ 0 := by
    rcases lt_or_eq_of_le hr_le_crossing with hr_lt | hr_eq
    · have hmono :
          binaryEndpointInverseGap
              (binaryEndpointSampleRateNat sampleRate 1)
              (binaryEndpointSampleRateNat sampleRate m) r <
            binaryEndpointInverseGap
              (binaryEndpointSampleRateNat sampleRate 1)
              (binaryEndpointSampleRateNat sampleRate m) crossing :=
        binaryEndpointInverseGap_strictMono hgFirst hgLast hr_lt
      rw [hcross] at hmono
      exact hmono.le
    · subst r
      rw [hcross]
  have hfirst_le_last :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r ≤
        binaryEndpointLastLevelOfRate
          (binaryEndpointSampleRateNat sampleRate m) r := by
    unfold binaryEndpointInverseGap at hgap_le
    linarith
  simpa [binaryEndpointForwardClippedCap, binaryEndpointSampleRateNat,
    lastAdjacentIndex, adjacentLowIndex] using hfirst_le_last

/--
On the endpoint-crossing shooting interval, every positive-index level in the
forward-clipped cascade is positive and no larger than the moving cap.
-/
theorem binaryEndpointForwardClippedLevelNat_pos_le_cap_of_le_inverseGap_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (hr_pos : 0 < r) (hr_le_crossing : r ≤ crossing)
    (n : ℕ) (hn_pos : 1 ≤ n) :
    0 <
        binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r n ∧
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r n ≤
        binaryEndpointForwardClippedCap sampleRate r := by
  have hfirst_mem :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r ∈ Set.Ioo (0 : ℝ) 1 :=
    binaryEndpointFirstLevelOfRate_mem_Ioo
      (hsample_pos 1 (by omega)) hr_pos
  have hfirst_le :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r ≤
        binaryEndpointForwardClippedCap sampleRate r :=
    binaryEndpointForwardClippedFirst_le_cap_of_le_inverseGap_crossing
      sampleRate (hsample_pos 1 (by omega)) (hsample_pos m (by omega))
      hcross hr_le_crossing
  exact
    ⟨binaryEndpointForwardClippedLevelNat_pos_of_first_pos_le_cap
        sampleRate (binaryEndpointForwardClippedCap sampleRate r) r
        hfirst_mem.1 hfirst_le n hn_pos,
      binaryEndpointForwardClippedLevelNat_le_cap_of_first_le_cap
        sampleRate (binaryEndpointForwardClippedCap sampleRate r) r
        hfirst_le n hn_pos⟩

/-- Penultimate forward-clipped level used by the terminal adjacent comparison. -/
def binaryEndpointForwardClippedPenultimateLevel {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) : ℝ :=
  binaryEndpointForwardClippedLevelNat sampleRate
    (binaryEndpointForwardClippedCap sampleRate r) r (m - 1)

/--
Terminal closed adjacent rate for the forward clipped cascade, before subtracting
the target rate to form the scalar gap.
-/
def binaryEndpointForwardClippedTerminalRate {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) : ℝ :=
  weightedBernoulliClosedThresholdRate
    (binaryEndpointSampleRateNat sampleRate m)
    (binaryEndpointSampleRateNat sampleRate (m - 1))
    (binaryEndpointForwardClippedCap sampleRate r)
    (binaryEndpointForwardClippedPenultimateLevel sampleRate r)

/--
Terminal scalar gap for the forward clipped cascade.  For `m > 1`, a zero of
this gap says that the final interior adjacent interval, ending at the last
endpoint-inverse cap, also realizes the target rate.
-/
def binaryEndpointForwardClippedTerminalGap {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) : ℝ :=
  binaryEndpointForwardClippedTerminalRate sampleRate r - r

/--
If the forward-clipped cascade has already collapsed to its cap at the first
interior level, the terminal scalar gap is `-r`.
-/
theorem binaryEndpointForwardClippedTerminalGap_eq_neg_of_first_eq_cap
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hfirst :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r =
        binaryEndpointForwardClippedCap sampleRate r)
    (hgHi : 0 < binaryEndpointSampleRateNat sampleRate m)
    (hgLo : 0 < binaryEndpointSampleRateNat sampleRate (m - 1))
    (hcap :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1) :
    binaryEndpointForwardClippedTerminalGap sampleRate r = -r := by
  let cap : ℝ := binaryEndpointForwardClippedCap sampleRate r
  have hlevel :
      binaryEndpointForwardClippedLevelNat sampleRate cap r (m - 1) =
        cap := by
    exact
      binaryEndpointForwardClippedLevelNat_eq_cap_of_first_eq_cap
        sampleRate cap r (by simpa [cap] using hfirst) (m - 1)
        (by omega)
  simp [binaryEndpointForwardClippedTerminalGap,
    binaryEndpointForwardClippedTerminalRate,
    binaryEndpointForwardClippedPenultimateLevel, cap, hlevel,
    weightedBernoulliClosedThresholdRate_self hgHi hgLo hcap.1 hcap.2]

/--
If the penultimate forward-clipped level has collapsed to the cap, then the
terminal scalar gap is `-r`.
-/
theorem binaryEndpointForwardClippedTerminalGap_eq_neg_of_penultimate_eq_cap
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hpenultimate :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) =
        binaryEndpointForwardClippedCap sampleRate r)
    (hgHi : 0 < binaryEndpointSampleRateNat sampleRate m)
    (hgLo : 0 < binaryEndpointSampleRateNat sampleRate (m - 1))
    (hcap :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1) :
    binaryEndpointForwardClippedTerminalGap sampleRate r = -r := by
  let cap : ℝ := binaryEndpointForwardClippedCap sampleRate r
  simp [binaryEndpointForwardClippedTerminalGap,
    binaryEndpointForwardClippedTerminalRate,
    binaryEndpointForwardClippedPenultimateLevel, hpenultimate,
    weightedBernoulliClosedThresholdRate_self hgHi hgLo hcap.1 hcap.2]

/--
At a positive zero of the terminal scalar gap, the penultimate level is strictly
below the cap.
-/
theorem binaryEndpointForwardClippedPenultimate_lt_cap_of_terminal_gap_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0)
    (hgHi : 0 < binaryEndpointSampleRateNat sampleRate m)
    (hgLo : 0 < binaryEndpointSampleRateNat sampleRate (m - 1))
    (hcap :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1)
    (hlevel_le :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) ≤
        binaryEndpointForwardClippedCap sampleRate r) :
    binaryEndpointForwardClippedLevelNat sampleRate
        (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
      binaryEndpointForwardClippedCap sampleRate r := by
  rcases lt_or_eq_of_le hlevel_le with hlt | heq
  · exact hlt
  · have hneg :
        binaryEndpointForwardClippedTerminalGap sampleRate r = -r :=
      binaryEndpointForwardClippedTerminalGap_eq_neg_of_penultimate_eq_cap
        hm sampleRate r heq hgHi hgLo hcap
    rw [hgap] at hneg
    linarith

/--
At the endpoint-inverse crossing, the forward-clipped terminal scalar gap is
negative for any chain with at least two interior levels.
-/
theorem binaryEndpointForwardClippedTerminalGap_neg_at_inverseGap_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) r = 0)
    (hgHi : 0 < binaryEndpointSampleRateNat sampleRate m)
    (hgLo : 0 < binaryEndpointSampleRateNat sampleRate (m - 1)) :
    binaryEndpointForwardClippedTerminalGap sampleRate r < 0 := by
  have hcap_eq :
      binaryEndpointForwardClippedCap sampleRate r =
        binaryEndpointLastLevelOfRate
          (binaryEndpointSampleRateNat sampleRate m) r := by
    simp [binaryEndpointForwardClippedCap, binaryEndpointSampleRateNat,
      lastAdjacentIndex, adjacentLowIndex]
  have hfirst :
      binaryEndpointFirstLevelOfRate
          (binaryEndpointSampleRateNat sampleRate 1) r =
        binaryEndpointForwardClippedCap sampleRate r := by
    unfold binaryEndpointInverseGap at hcross
    rw [hcap_eq]
    linarith
  have hcap :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hcap_eq]
    exact binaryEndpointLastLevelOfRate_mem_Ioo hgHi hr
  rw [
    binaryEndpointForwardClippedTerminalGap_eq_neg_of_first_eq_cap
      hm sampleRate r hfirst hgHi hgLo hcap]
  linarith

/-- For two interior levels, the forward-cascade terminal gap is the scalar middle gap. -/
theorem binaryEndpointForwardClippedTerminalGap_two_eq
    (sampleRate : Fin (2 + 2) → ℝ) (r : ℝ) :
    binaryEndpointForwardClippedTerminalGap sampleRate r =
      binaryEndpointTwoInteriorMiddleRateGap
        (sampleRate (adjacentLowIndex (1 : Fin (2 + 1))))
        (sampleRate (adjacentHighIndex (1 : Fin (2 + 1)))) r := by
  simp [binaryEndpointForwardClippedTerminalGap,
    binaryEndpointForwardClippedTerminalRate,
    binaryEndpointForwardClippedPenultimateLevel,
    binaryEndpointForwardClippedCap,
    binaryEndpointTwoInteriorMiddleRateGap,
    binaryEndpointTwoInteriorMiddleRate,
    binaryEndpointForwardClippedLevelNat,
    binaryEndpointSampleRateNat, adjacentLowIndex, adjacentHighIndex,
    lastAdjacentIndex]

/-- The forward-cascade cap tends to the upper endpoint as the target rate tends to zero. -/
theorem binaryEndpointForwardClippedCap_tendsto_nhdsGT_zero {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) :
    Filter.Tendsto
      (fun r : ℝ => binaryEndpointForwardClippedCap sampleRate r)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  let gLast : ℝ := binaryEndpointSampleRateNat sampleRate m
  have hcont :
      Filter.Tendsto (fun r : ℝ => binaryEndpointLastLevelOfRate gLast r)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hcontinuous :
        ContinuousAt (binaryEndpointLastLevelOfRate gLast) (0 : ℝ) :=
      (binaryEndpointLastLevelOfRate_continuous gLast).continuousAt
    simpa [gLast, binaryEndpointLastLevelOfRate] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  convert hcont using 1
  ext r
  simp [binaryEndpointForwardClippedCap, gLast,
    binaryEndpointSampleRateNat, lastAdjacentIndex, adjacentLowIndex]

/--
Every fixed positive index in the forward-clipped cascade tends to the lower
endpoint as the target rate tends to zero from above, and is eventually inside
the weak bracket below the cap.
-/
theorem binaryEndpointForwardClippedLevelNat_tendsto_zero_and_eventually_pos_le_cap
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (n : ℕ) (hn_pos : 1 ≤ n) (hn_bound : n < m + 2) :
    Filter.Tendsto
        (fun r : ℝ =>
          binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r n)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 <
          binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r n ∧
        binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r n ≤
          binaryEndpointForwardClippedCap sampleRate r := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          have hfirst_tendsto :
              Filter.Tendsto
                (fun r : ℝ =>
                  binaryEndpointFirstLevelOfRate
                    (binaryEndpointSampleRateNat sampleRate 1) r)
                (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
            have hcontinuous :
                ContinuousAt
                  (binaryEndpointFirstLevelOfRate
                    (binaryEndpointSampleRateNat sampleRate 1)) (0 : ℝ) :=
              (binaryEndpointFirstLevelOfRate_continuous
                (binaryEndpointSampleRateNat sampleRate 1)).continuousAt
            simpa [binaryEndpointFirstLevelOfRate] using
              hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
          have hcap_tendsto :=
            binaryEndpointForwardClippedCap_tendsto_nhdsGT_zero sampleRate
          have hfirst_lt_half :
              ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
                binaryEndpointFirstLevelOfRate
                    (binaryEndpointSampleRateNat sampleRate 1) r < (1 / 2 : ℝ) :=
            hfirst_tendsto.eventually
              (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
          have hcap_gt_half :
              ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
                (1 / 2 : ℝ) < binaryEndpointForwardClippedCap sampleRate r :=
            hcap_tendsto.eventually
              (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
          have hvalid :
              ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
                0 <
                  binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate r) r 1 ∧
                binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate r) r 1 ≤
                  binaryEndpointForwardClippedCap sampleRate r := by
            filter_upwards
              [self_mem_nhdsWithin, hfirst_lt_half, hcap_gt_half]
              with r hr hfirst_half hcap_half
            have hfirst_mem :
                binaryEndpointFirstLevelOfRate
                    (binaryEndpointSampleRateNat sampleRate 1) r ∈
                  Set.Ioo (0 : ℝ) 1 :=
              binaryEndpointFirstLevelOfRate_mem_Ioo
                (hsample_pos 1 (by omega)) hr
            constructor
            · simpa [binaryEndpointForwardClippedLevelNat] using hfirst_mem.1
            · simp [binaryEndpointForwardClippedLevelNat]
              exact le_of_lt (hfirst_half.trans hcap_half)
          constructor
          · simpa [binaryEndpointForwardClippedLevelNat] using hfirst_tendsto
          · exact hvalid
      | succ n =>
          have hn1_pos : 1 ≤ n + 1 := by omega
          have hn1_bound : n + 1 < m + 2 := by omega
          rcases ih hn1_pos hn1_bound with ⟨hprev_tendsto, hprev_valid⟩
          have hcap_tendsto :=
            binaryEndpointForwardClippedCap_tendsto_nhdsGT_zero sampleRate
          have htarget_tendsto :
              Filter.Tendsto (fun r : ℝ => r)
                (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
            Filter.tendsto_id.mono_left nhdsWithin_le_nhds
          have hcap_lt_one :
              ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
                binaryEndpointForwardClippedCap sampleRate r < 1 := by
            filter_upwards [self_mem_nhdsWithin] with r hr
            have hsample_m :
                0 <
                  sampleRate
                    (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
              simpa [binaryEndpointSampleRateNat, lastAdjacentIndex,
                adjacentLowIndex] using hsample_pos m (by omega)
            have hcap_mem :
                binaryEndpointForwardClippedCap sampleRate r ∈
                  Set.Ioo (0 : ℝ) 1 := by
              simpa [binaryEndpointForwardClippedCap, lastAdjacentIndex,
                adjacentLowIndex] using
                binaryEndpointLastLevelOfRate_mem_Ioo hsample_m hr
            exact hcap_mem.2
          have htarget_pos :
              ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r :=
            self_mem_nhdsWithin
          have hselector_valid :
              ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
                0 <
                    binaryEndpointForwardClippedLevelNat sampleRate
                      (binaryEndpointForwardClippedCap sampleRate r) r (n + 1) ∧
                  binaryEndpointForwardClippedLevelNat sampleRate
                      (binaryEndpointForwardClippedCap sampleRate r) r (n + 1) ≤
                    binaryEndpointForwardClippedCap sampleRate r ∧
                  binaryEndpointForwardClippedCap sampleRate r < 1 ∧
                  0 < r := by
            filter_upwards [hprev_valid, hcap_lt_one, htarget_pos]
              with r hprev hcap1 hr
            exact ⟨hprev.1, hprev.2, hcap1, hr⟩
          have hnext_tendsto :
              Filter.Tendsto
                (fun r : ℝ =>
                  weightedBernoulliHighEndpointOfRateOrCap
                    (binaryEndpointSampleRateNat sampleRate (n + 2))
                    (binaryEndpointSampleRateNat sampleRate (n + 1))
                    (binaryEndpointForwardClippedLevelNat sampleRate
                      (binaryEndpointForwardClippedCap sampleRate r) r
                      (n + 1))
                    (binaryEndpointForwardClippedCap sampleRate r) r)
                (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
            weightedBernoulliHighEndpointOfRateOrCap_tendsto_zero_of_low_target_tendsto_zero
              (hsample_pos (n + 2) (by omega))
              (hsample_pos (n + 1) (by omega))
              (by norm_num : (0 : ℝ) < 1)
              hprev_tendsto hcap_tendsto htarget_tendsto hselector_valid
          have hnext_valid :
              ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
                0 <
                  binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate r) r
                    (n + 2) ∧
                binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate r) r
                    (n + 2) ≤
                  binaryEndpointForwardClippedCap sampleRate r := by
            filter_upwards [hprev_valid] with r hprev
            change
              0 <
                  weightedBernoulliHighEndpointOfRateOrCap
                    (binaryEndpointSampleRateNat sampleRate (n + 2))
                    (binaryEndpointSampleRateNat sampleRate (n + 1))
                    (binaryEndpointForwardClippedLevelNat sampleRate
                      (binaryEndpointForwardClippedCap sampleRate r) r
                      (n + 1))
                    (binaryEndpointForwardClippedCap sampleRate r) r ∧
                weightedBernoulliHighEndpointOfRateOrCap
                    (binaryEndpointSampleRateNat sampleRate (n + 2))
                    (binaryEndpointSampleRateNat sampleRate (n + 1))
                    (binaryEndpointForwardClippedLevelNat sampleRate
                      (binaryEndpointForwardClippedCap sampleRate r) r
                      (n + 1))
                    (binaryEndpointForwardClippedCap sampleRate r) r ≤
                  binaryEndpointForwardClippedCap sampleRate r
            exact
              ⟨hprev.1.trans_le
                  (le_weightedBernoulliHighEndpointOfRateOrCap hprev.2),
                weightedBernoulliHighEndpointOfRateOrCap_le_cap hprev.2⟩
          constructor
          · simpa [binaryEndpointForwardClippedLevelNat] using hnext_tendsto
          · exact hnext_valid

/--
For any finite endpoint-aware chain with at least two interior levels, the
forward-clipped terminal gap is eventually positive near target rate zero.
-/
theorem binaryEndpointForwardClippedTerminalGap_eventually_pos_nhdsGT_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < binaryEndpointForwardClippedTerminalGap sampleRate r := by
  have hlevel :=
    binaryEndpointForwardClippedLevelNat_tendsto_zero_and_eventually_pos_le_cap
      sampleRate hsample_pos (m - 1) (by omega) (by omega)
  have hlevel_tendsto := hlevel.1
  have hlevel_valid := hlevel.2
  have hcap_tendsto :=
    binaryEndpointForwardClippedCap_tendsto_nhdsGT_zero sampleRate
  have hrate_tendsto :
      Filter.Tendsto
        (fun r : ℝ =>
          weightedBernoulliClosedThresholdRate
            (binaryEndpointSampleRateNat sampleRate m)
            (binaryEndpointSampleRateNat sampleRate (m - 1))
            (binaryEndpointForwardClippedCap sampleRate r)
            (binaryEndpointForwardClippedLevelNat sampleRate
              (binaryEndpointForwardClippedCap sampleRate r) r (m - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    have hvalid :
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1 ∧
            binaryEndpointForwardClippedLevelNat sampleRate
              (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) ∈
                Set.Ioo (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin, hlevel_valid] with r hr hlevel_valid
      have hcap_mem :
          binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1 := by
        have hsample_m :
            0 <
              sampleRate
                (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
          simpa [binaryEndpointSampleRateNat, lastAdjacentIndex,
            adjacentLowIndex] using hsample_pos m (by omega)
        simp [binaryEndpointForwardClippedCap, lastAdjacentIndex,
          adjacentLowIndex]
        exact binaryEndpointLastLevelOfRate_mem_Ioo
          hsample_m hr
      exact
        ⟨hcap_mem,
          ⟨hlevel_valid.1,
            hlevel_valid.2.trans_lt hcap_mem.2⟩⟩
    exact
      weightedBernoulliClosedThresholdRate_tendsto_atTop_of_hi_tendsto_one_lo_tendsto_zero
        (hsample_pos m (by omega))
        (hsample_pos (m - 1) (by omega))
        hcap_tendsto hlevel_tendsto hvalid
  have hrate_gt_one :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        1 <
          weightedBernoulliClosedThresholdRate
            (binaryEndpointSampleRateNat sampleRate m)
            (binaryEndpointSampleRateNat sampleRate (m - 1))
            (binaryEndpointForwardClippedCap sampleRate r)
            (binaryEndpointForwardClippedLevelNat sampleRate
              (binaryEndpointForwardClippedCap sampleRate r) r (m - 1)) :=
    hrate_tendsto.eventually_gt_atTop (1 : ℝ)
  have hr_lt_one :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < 1 := by
    have hid :
        Filter.Tendsto (fun r : ℝ => r)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    exact hid.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hrate_gt_one, hr_lt_one] with r hrate_gt hr_lt
  dsimp [binaryEndpointForwardClippedTerminalGap,
    binaryEndpointForwardClippedTerminalRate,
    binaryEndpointForwardClippedPenultimateLevel]
  linarith

/-- There is a positive target rate where the forward-clipped terminal gap is positive. -/
theorem binaryEndpointForwardClippedTerminalGap_exists_pos
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃ r : ℝ, 0 < r ∧
      0 < binaryEndpointForwardClippedTerminalGap sampleRate r := by
  have hev :=
    binaryEndpointForwardClippedTerminalGap_eventually_pos_nhdsGT_zero
      hm sampleRate hsample_pos
  have hpos :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r :=
    self_mem_nhdsWithin
  exact (hpos.and hev).exists

/--
Forward-cascade scalar IVT package: once terminal-gap continuity is available
on the shooting interval, the lower and upper signs produce a positive zero.
-/
theorem binaryEndpointForwardClippedTerminalGap_exists_zero_of_continuousOn
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing : ℝ}
    (hcrossing : 0 < crossing)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (hcont :
      ∀ left : ℝ, 0 < left → left < crossing →
        ContinuousOn (fun r : ℝ =>
          binaryEndpointForwardClippedTerminalGap sampleRate r)
          (Set.Icc left crossing)) :
    ∃ r : ℝ, 0 < r ∧ r < crossing ∧
      binaryEndpointForwardClippedTerminalGap sampleRate r = 0 := by
  have hpositive_eventually :=
    binaryEndpointForwardClippedTerminalGap_eventually_pos_nhdsGT_zero
      hm sampleRate hsample_pos
  have hwithin :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 < r ∧ r < crossing ∧
          0 < binaryEndpointForwardClippedTerminalGap sampleRate r := by
    have hpos :
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r :=
      self_mem_nhdsWithin
    have hlt_crossing :
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < crossing := by
      have hid :
          Filter.Tendsto (fun r : ℝ => r)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        Filter.tendsto_id.mono_left nhdsWithin_le_nhds
      exact hid.eventually (eventually_lt_nhds hcrossing)
    filter_upwards [hpos, hlt_crossing, hpositive_eventually]
      with r hr_pos hr_cross hgap_pos
    exact ⟨hr_pos, hr_cross, hgap_pos⟩
  rcases hwithin.exists with ⟨left, hleft_pos, hleft_lt_crossing, hleft_gap⟩
  have hcross_gap_neg :
      binaryEndpointForwardClippedTerminalGap sampleRate crossing < 0 :=
    binaryEndpointForwardClippedTerminalGap_neg_at_inverseGap_crossing
      hm sampleRate hcrossing hcross
      (hsample_pos m (by omega)) (hsample_pos (m - 1) (by omega))
  let gap : ℝ → ℝ := fun r =>
    binaryEndpointForwardClippedTerminalGap sampleRate r
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (gap crossing) (gap left) := by
    exact ⟨le_of_lt hcross_gap_neg, hleft_gap.le⟩
  rcases
    intermediate_value_Icc' (le_of_lt hleft_lt_crossing)
      (hcont left hleft_pos hleft_lt_crossing) hzero_mem with
    ⟨root, hroot_mem, hroot_gap⟩
  have hroot_pos : 0 < root := hleft_pos.trans_le hroot_mem.1
  have hroot_lt_crossing : root < crossing := by
    have hne : root ≠ crossing := by
      intro h
      subst root
      dsimp [gap] at hroot_gap
      linarith
    exact lt_of_le_of_ne hroot_mem.2 hne
  exact ⟨root, hroot_pos, hroot_lt_crossing, hroot_gap⟩

/--
On the endpoint-crossing shooting interval, every fixed forward-clipped level is
continuous in the target rate.
-/
theorem binaryEndpointForwardClippedLevelNat_continuousAt_of_le_inverseGap_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (hr_pos : 0 < r) (hr_le_crossing : r ≤ crossing)
    (n : ℕ) (hn_bound : n < m + 2) :
    ContinuousAt
      (fun s : ℝ =>
        binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate s) s n) r := by
  induction n with
  | zero =>
      simpa [binaryEndpointForwardClippedLevelNat] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) r)
  | succ n ih =>
      cases n with
      | zero =>
          simpa [binaryEndpointForwardClippedLevelNat] using
            (binaryEndpointFirstLevelOfRate_continuous
              (binaryEndpointSampleRateNat sampleRate 1)).continuousAt
      | succ n =>
          have hprev_cont :
              ContinuousAt
                (fun s : ℝ =>
                  binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate s) s (n + 1))
                r :=
            ih (by omega)
          have hcap_cont :
              ContinuousAt
                (fun s : ℝ => binaryEndpointForwardClippedCap sampleRate s) r :=
            (binaryEndpointForwardClippedCap_continuous sampleRate).continuousAt
          have hprev_bounds :
              0 <
                  binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate r) r
                    (n + 1) ∧
                binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate r) r
                    (n + 1) ≤
                  binaryEndpointForwardClippedCap sampleRate r :=
            binaryEndpointForwardClippedLevelNat_pos_le_cap_of_le_inverseGap_crossing
              hm sampleRate hsample_pos hcross hr_pos hr_le_crossing
              (n + 1) (by omega)
          have hcap_mem :
              binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1 := by
            have hsample_m :
                0 <
                  sampleRate
                    (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
              simpa [binaryEndpointSampleRateNat, lastAdjacentIndex,
                adjacentLowIndex] using hsample_pos m (by omega)
            simpa [binaryEndpointForwardClippedCap] using
              binaryEndpointLastLevelOfRate_mem_Ioo hsample_m hr_pos
          have hselector :
              ContinuousAt
                (fun q : ℝ × ℝ × ℝ =>
                  weightedBernoulliHighEndpointOfRateOrCap
                    (binaryEndpointSampleRateNat sampleRate (n + 2))
                    (binaryEndpointSampleRateNat sampleRate (n + 1))
                    q.1 q.2.1 q.2.2)
                (binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate r) r
                    (n + 1),
                  binaryEndpointForwardClippedCap sampleRate r,
                  r) :=
            weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params
              (hsample_pos (n + 2) (by omega))
              (hsample_pos (n + 1) (by omega))
              hprev_bounds.1 hprev_bounds.2 hcap_mem.2 hr_pos
          have hpair :
              ContinuousAt
                (fun s : ℝ =>
                  (binaryEndpointForwardClippedLevelNat sampleRate
                      (binaryEndpointForwardClippedCap sampleRate s) s
                      (n + 1),
                    binaryEndpointForwardClippedCap sampleRate s,
                    s))
                r :=
            hprev_cont.prodMk (hcap_cont.prodMk continuousAt_id)
          change
            ContinuousAt
              (fun s : ℝ =>
                weightedBernoulliHighEndpointOfRateOrCap
                  (binaryEndpointSampleRateNat sampleRate (n + 2))
                  (binaryEndpointSampleRateNat sampleRate (n + 1))
                  (binaryEndpointForwardClippedLevelNat sampleRate
                    (binaryEndpointForwardClippedCap sampleRate s) s
                    (n + 1))
                  (binaryEndpointForwardClippedCap sampleRate s) s)
              r
          exact hselector.comp_of_eq hpair rfl

/-- Continuous-on form of the forward-clipped level continuity theorem. -/
theorem binaryEndpointForwardClippedLevelNat_continuousOn_Icc_of_inverseGap_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {left crossing : ℝ} (hleft_pos : 0 < left)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (n : ℕ) (hn_bound : n < m + 2) :
    ContinuousOn
      (fun r : ℝ =>
        binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r n)
      (Set.Icc left crossing) := by
  intro r hr
  exact
    (binaryEndpointForwardClippedLevelNat_continuousAt_of_le_inverseGap_crossing
      hm sampleRate hsample_pos hcross (hleft_pos.trans_le hr.1) hr.2
      n hn_bound).continuousWithinAt

/-- Continuity of the named penultimate forward-clipped level. -/
theorem binaryEndpointForwardClippedPenultimateLevel_continuousAt_of_le_inverseGap_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (hr_pos : 0 < r) (hr_le_crossing : r ≤ crossing) :
    ContinuousAt
      (fun s : ℝ => binaryEndpointForwardClippedPenultimateLevel sampleRate s) r := by
  change
    ContinuousAt
      (fun s : ℝ =>
        binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate s) s (m - 1)) r
  exact
    binaryEndpointForwardClippedLevelNat_continuousAt_of_le_inverseGap_crossing
      hm sampleRate hsample_pos hcross hr_pos hr_le_crossing (m - 1) (by omega)

/--
Continuous-on form of the terminal forward-cascade closed-rate expression,
before repackaging it as the named terminal gap.
-/
theorem binaryEndpointForwardClippedTerminalRateSub_continuousOn_Icc_of_inverseGap_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {left crossing : ℝ} (hleft_pos : 0 < left)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0) :
    ContinuousOn
      (fun r : ℝ =>
        weightedBernoulliClosedThresholdRate
          (binaryEndpointSampleRateNat sampleRate m)
          (binaryEndpointSampleRateNat sampleRate (m - 1))
          (binaryEndpointForwardClippedCap sampleRate r)
          (binaryEndpointForwardClippedPenultimateLevel sampleRate r) -
        r)
      (Set.Icc left crossing) := by
  intro r hr
  have hr_pos : 0 < r := hleft_pos.trans_le hr.1
  have hlevel_cont :
      ContinuousWithinAt
        (fun s : ℝ => binaryEndpointForwardClippedPenultimateLevel sampleRate s)
        (Set.Icc left crossing) r :=
    (binaryEndpointForwardClippedPenultimateLevel_continuousAt_of_le_inverseGap_crossing
      hm sampleRate hsample_pos hcross hr_pos hr.2).continuousWithinAt
  have hcap_cont :
      ContinuousWithinAt
        (fun s : ℝ => binaryEndpointForwardClippedCap sampleRate s)
        (Set.Icc left crossing) r :=
    (binaryEndpointForwardClippedCap_continuous sampleRate).continuousAt.continuousWithinAt
  have hpair_cont :
      ContinuousWithinAt
        (fun s : ℝ =>
          (binaryEndpointForwardClippedCap sampleRate s,
            binaryEndpointForwardClippedPenultimateLevel sampleRate s))
        (Set.Icc left crossing) r :=
    hcap_cont.prodMk hlevel_cont
  have hlevel_bounds :
      0 <
          binaryEndpointForwardClippedPenultimateLevel sampleRate r ∧
        binaryEndpointForwardClippedPenultimateLevel sampleRate r ≤
          binaryEndpointForwardClippedCap sampleRate r := by
    simpa [binaryEndpointForwardClippedPenultimateLevel] using
      binaryEndpointForwardClippedLevelNat_pos_le_cap_of_le_inverseGap_crossing
        hm sampleRate hsample_pos hcross hr_pos hr.2 (m - 1) (by omega)
  have hcap_mem :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1 := by
    have hsample_m :
        0 <
          sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
      simpa [binaryEndpointSampleRateNat, lastAdjacentIndex, adjacentLowIndex]
        using hsample_pos m (by omega)
    simpa [binaryEndpointForwardClippedCap] using
      binaryEndpointLastLevelOfRate_mem_Ioo hsample_m hr_pos
  have hrate_at :
      ContinuousAt
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate
            (binaryEndpointSampleRateNat sampleRate m)
            (binaryEndpointSampleRateNat sampleRate (m - 1))
            q.1 q.2)
        (binaryEndpointForwardClippedCap sampleRate r,
          binaryEndpointForwardClippedPenultimateLevel sampleRate r) :=
    weightedBernoulliClosedThresholdRate_continuousAt_pair
      (gHi := binaryEndpointSampleRateNat sampleRate m)
      (gLo := binaryEndpointSampleRateNat sampleRate (m - 1))
      (pHi := binaryEndpointForwardClippedCap sampleRate r)
      (pLo := binaryEndpointForwardClippedPenultimateLevel sampleRate r)
      hcap_mem.1 hcap_mem.2 hlevel_bounds.1
      (lt_of_le_of_lt hlevel_bounds.2 hcap_mem.2)
  have hrate_within :
      ContinuousWithinAt
        (fun s : ℝ =>
          weightedBernoulliClosedThresholdRate
            (binaryEndpointSampleRateNat sampleRate m)
            (binaryEndpointSampleRateNat sampleRate (m - 1))
            (binaryEndpointForwardClippedCap sampleRate s)
            (binaryEndpointForwardClippedPenultimateLevel sampleRate s))
        (Set.Icc left crossing) r := by
    simpa [Function.comp_def] using
      (ContinuousAt.comp_continuousWithinAt
        (x := r) (s := Set.Icc left crossing)
        (f := fun s : ℝ =>
          (binaryEndpointForwardClippedCap sampleRate s,
            binaryEndpointForwardClippedPenultimateLevel sampleRate s))
        hrate_at hpair_cont)
  exact hrate_within.sub continuousWithinAt_id

/--
Forward-cascade scalar existence with the shooting-interval continuity supplied
by the recursive clipped-level construction.
-/
theorem binaryEndpointForwardClippedTerminalGap_exists_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing : ℝ}
    (hcrossing : 0 < crossing)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0) :
    ∃ r : ℝ, 0 < r ∧ r < crossing ∧
      binaryEndpointForwardClippedTerminalGap sampleRate r = 0 := by
  let gapExpr : ℝ → ℝ := fun r =>
    weightedBernoulliClosedThresholdRate
        (binaryEndpointSampleRateNat sampleRate m)
        (binaryEndpointSampleRateNat sampleRate (m - 1))
        (binaryEndpointForwardClippedCap sampleRate r)
        (binaryEndpointForwardClippedPenultimateLevel sampleRate r) -
      r
  have hpositive_eventually :=
    binaryEndpointForwardClippedTerminalGap_eventually_pos_nhdsGT_zero
      hm sampleRate hsample_pos
  have hwithin :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 < r ∧ r < crossing ∧ 0 < gapExpr r := by
    have hpos :
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r :=
      self_mem_nhdsWithin
    have hlt_crossing :
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < crossing := by
      have hid :
          Filter.Tendsto (fun r : ℝ => r)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        Filter.tendsto_id.mono_left nhdsWithin_le_nhds
      exact hid.eventually (eventually_lt_nhds hcrossing)
    filter_upwards [hpos, hlt_crossing, hpositive_eventually]
      with r hr_pos hr_cross hgap_pos
    have hgap_pos_expr : 0 < gapExpr r := by
      dsimp [gapExpr]
      simpa [binaryEndpointForwardClippedTerminalGap,
        binaryEndpointForwardClippedTerminalRate] using hgap_pos
    exact ⟨hr_pos, hr_cross, hgap_pos_expr⟩
  rcases hwithin.exists with ⟨left, hleft_pos, hleft_lt_crossing, hleft_gap⟩
  have hcross_gap_named :
      binaryEndpointForwardClippedTerminalGap sampleRate crossing < 0 :=
    binaryEndpointForwardClippedTerminalGap_neg_at_inverseGap_crossing
      hm sampleRate hcrossing hcross
      (hsample_pos m (by omega)) (hsample_pos (m - 1) (by omega))
  have hcross_gap : gapExpr crossing < 0 := by
    dsimp [gapExpr]
    simpa [binaryEndpointForwardClippedTerminalGap,
      binaryEndpointForwardClippedTerminalRate] using hcross_gap_named
  have hcont : ContinuousOn gapExpr (Set.Icc left crossing) := by
    dsimp [gapExpr]
    exact
      binaryEndpointForwardClippedTerminalRateSub_continuousOn_Icc_of_inverseGap_crossing
        hm sampleRate hsample_pos hleft_pos hcross
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (gapExpr crossing) (gapExpr left) := by
    exact ⟨le_of_lt hcross_gap, hleft_gap.le⟩
  rcases
    intermediate_value_Icc' (le_of_lt hleft_lt_crossing)
      hcont hzero_mem with
    ⟨root, hroot_mem, hroot_gap_expr⟩
  have hroot_pos : 0 < root := hleft_pos.trans_le hroot_mem.1
  have hroot_lt_crossing : root < crossing := by
    have hne : root ≠ crossing := by
      intro h
      subst root
      linarith
    exact lt_of_le_of_ne hroot_mem.2 hne
  have hroot_gap :
      binaryEndpointForwardClippedTerminalGap sampleRate root = 0 := by
    dsimp [gapExpr] at hroot_gap_expr
    simpa [binaryEndpointForwardClippedTerminalGap,
      binaryEndpointForwardClippedTerminalRate] using hroot_gap_expr
  exact ⟨root, hroot_pos, hroot_lt_crossing, hroot_gap⟩

/--
At a positive zero of the terminal forward-cascade gap, every nonterminal
clipped selector step is genuinely feasible.  Otherwise that step would clip to
the moving cap, all later positive levels would remain at the cap, and the
terminal gap would be `-r`.
-/
theorem binaryEndpointForwardClippedLevelNat_step_feasible_of_terminal_gap_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {r : ℝ} (hr_pos : 0 < r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0)
    (n : ℕ) (hn : n + 2 < m) :
    WeightedBernoulliHighEndpointTargetFeasible
      (binaryEndpointSampleRateNat sampleRate (n + 2))
      (binaryEndpointSampleRateNat sampleRate (n + 1))
      (binaryEndpointForwardClippedLevelNat sampleRate
        (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
      (binaryEndpointForwardClippedCap sampleRate r) r := by
  by_contra hnot
  have hnext_eq :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (n + 2) =
        binaryEndpointForwardClippedCap sampleRate r := by
    change
      weightedBernoulliHighEndpointOfRateOrCap
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r =
        binaryEndpointForwardClippedCap sampleRate r
    exact weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible hnot
  have hpenultimate_eq :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) =
        binaryEndpointForwardClippedCap sampleRate r :=
    binaryEndpointForwardClippedLevelNat_eq_cap_of_eq_cap
      sampleRate (binaryEndpointForwardClippedCap sampleRate r) r
      (k := n + 2) (by omega) hnext_eq (m - 1) (by omega)
  have hcap_mem :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1 := by
    have hsample_m :
        0 <
          sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
      simpa [binaryEndpointSampleRateNat, lastAdjacentIndex, adjacentLowIndex]
        using hsample_pos m (by omega)
    simpa [binaryEndpointForwardClippedCap] using
      binaryEndpointLastLevelOfRate_mem_Ioo hsample_m hr_pos
  have hneg :
      binaryEndpointForwardClippedTerminalGap sampleRate r = -r :=
    binaryEndpointForwardClippedTerminalGap_eq_neg_of_penultimate_eq_cap
      hm sampleRate r hpenultimate_eq
      (hsample_pos m (by omega)) (hsample_pos (m - 1) (by omega))
      hcap_mem
  rw [hgap] at hneg
  linarith

/--
On the endpoint-inverse shooting interval, a positive zero of the terminal
forward-cascade gap gives the strict terminal order needed by the scalar
certificate.
-/
theorem binaryEndpointForwardClippedPenultimate_lt_cap_of_terminal_gap_zero_of_le_inverseGap_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (hr_pos : 0 < r) (hr_le_crossing : r ≤ crossing)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    binaryEndpointForwardClippedLevelNat sampleRate
        (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
      binaryEndpointForwardClippedCap sampleRate r := by
  have hlevel_bounds :
      0 <
          binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) ∧
        binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) ≤
          binaryEndpointForwardClippedCap sampleRate r :=
    binaryEndpointForwardClippedLevelNat_pos_le_cap_of_le_inverseGap_crossing
      hm sampleRate hsample_pos hcross hr_pos hr_le_crossing (m - 1) (by omega)
  have hcap_mem :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1 := by
    have hsample_m :
        0 <
          sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
      simpa [binaryEndpointSampleRateNat, lastAdjacentIndex, adjacentLowIndex]
        using hsample_pos m (by omega)
    simpa [binaryEndpointForwardClippedCap] using
      binaryEndpointLastLevelOfRate_mem_Ioo hsample_m hr_pos
  exact
    binaryEndpointForwardClippedPenultimate_lt_cap_of_terminal_gap_zero
      hm sampleRate hr_pos hgap
      (hsample_pos m (by omega)) (hsample_pos (m - 1) (by omega))
      hcap_mem hlevel_bounds.2

@[simp] theorem binaryEndpointSampleRateNat_of_lt {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) {n : ℕ} (hn : n < m + 2) :
    binaryEndpointSampleRateNat sampleRate n = sampleRate ⟨n, hn⟩ := by
  simp [binaryEndpointSampleRateNat, hn]

/-- Convert support-safe natural-index positivity to adjacent-high positivity. -/
theorem binaryEndpointSampleRateNat_pos_adjacentHigh {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) := by
  intro i
  have hraw := hsample_pos (i.val + 1) (by omega)
  rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
  simpa [adjacentHighIndex] using hraw

/-- Convert support-safe natural-index positivity to adjacent-low positivity. -/
theorem binaryEndpointSampleRateNat_pos_adjacentLow {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) := by
  intro i
  have hraw := hsample_pos i.val (by omega)
  rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
  simpa [adjacentLowIndex] using hraw

@[simp] theorem binaryEndpointForwardClippedLevelNat_zero {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ) :
    binaryEndpointForwardClippedLevelNat sampleRate cap r 0 = 0 := by
  rfl

@[simp] theorem binaryEndpointForwardClippedLevelNat_one {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ) :
    binaryEndpointForwardClippedLevelNat sampleRate cap r 1 =
      binaryEndpointFirstLevelOfRate
        (binaryEndpointSampleRateNat sampleRate 1) r := by
  rfl

theorem binaryEndpointForwardClippedLevels_first {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) :
    binaryEndpointForwardClippedLevels sampleRate r
        (firstLevelIndex : Fin (m + 2)) =
      0 := by
  simp [binaryEndpointForwardClippedLevels, firstLevelIndex]

theorem binaryEndpointForwardClippedLevels_last {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) :
    binaryEndpointForwardClippedLevels sampleRate r
        (lastLevelIndex : Fin (m + 2)) =
      1 := by
  simp [binaryEndpointForwardClippedLevels, lastLevelIndex]

theorem binaryEndpointForwardClippedLevels_eq_levelNat_of_val_lt_m {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (i : Fin (m + 2)) (hi : i.val < m) :
    binaryEndpointForwardClippedLevels sampleRate r i =
      binaryEndpointForwardClippedLevelNat sampleRate
        (binaryEndpointForwardClippedCap sampleRate r) r i.val := by
  have hnot_last : i.val ≠ m + 1 := by omega
  have hnot_cap : i.val ≠ m := by omega
  by_cases hzero : i.val = 0
  · have hi_zero : i = (0 : Fin (m + 2)) := by
      ext
      simpa using hzero
    simp [binaryEndpointForwardClippedLevels, binaryEndpointForwardClippedCap,
      hi_zero]
  · have hi_not_zero : i ≠ (0 : Fin (m + 2)) := by
      intro hi_zero
      exact hzero (by simpa using congrArg Fin.val hi_zero)
    simp [binaryEndpointForwardClippedLevels, binaryEndpointForwardClippedCap,
      hi_not_zero, hnot_last, hnot_cap]

theorem binaryEndpointForwardClippedLevels_first_high {m : ℕ}
    (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) :
    binaryEndpointForwardClippedLevels sampleRate r
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) =
      binaryEndpointFirstLevelOfRate
        (sampleRate
          (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) r := by
  have h1_lt : 1 < m + 2 := by omega
  have hm_ne_zero : m ≠ 0 := by omega
  have hnot_cap : (1 : ℕ) ≠ m := by omega
  simp [binaryEndpointForwardClippedLevels, firstAdjacentIndex,
    adjacentHighIndex, binaryEndpointSampleRateNat, h1_lt,
    hm_ne_zero, hnot_cap]

theorem binaryEndpointForwardClippedLevels_last_low {m : ℕ}
    (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) :
    binaryEndpointForwardClippedLevels sampleRate r
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
      binaryEndpointForwardClippedCap sampleRate r := by
  simp [binaryEndpointForwardClippedLevels, binaryEndpointForwardClippedCap,
    lastAdjacentIndex,
    adjacentLowIndex, Nat.ne_of_gt hm]

/-- The first adjacent rate of the clipped forward vector realizes the target rate. -/
theorem binaryEndpointForwardClippedLevels_first_rate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hsample :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointAwareAdjacentRate
        (binaryEndpointForwardClippedLevels sampleRate r) sampleRate
        (firstAdjacentIndex : Fin (m + 1)) =
      r := by
  let levels : Fin (m + 2) → ℝ :=
    binaryEndpointForwardClippedLevels sampleRate r
  let first : Fin (m + 1) := firstAdjacentIndex
  let high : Fin (m + 2) := adjacentHighIndex first
  have hlevel : levels high =
      binaryEndpointFirstLevelOfRate (sampleRate high) r := by
    dsimp [levels, high, first]
    simpa using
      binaryEndpointForwardClippedLevels_first_high hm sampleRate r
  have hrate :
      sampleRate high *
          (-Real.log (1 - binaryEndpointFirstLevelOfRate (sampleRate high) r)) =
        r :=
    binaryEndpointFirstLevelOfRate_realizes hsample
  calc
    binaryEndpointAwareAdjacentRate levels sampleRate first =
        sampleRate high * (-Real.log (1 - levels high)) := by
          simpa [first, high] using
            binaryEndpointAwareAdjacentRate_first
              levels sampleRate first (by simp [first])
    _ = sampleRate high *
        (-Real.log (1 - binaryEndpointFirstLevelOfRate (sampleRate high) r)) := by
          rw [hlevel]
    _ = r := hrate

/-- The last adjacent rate of the clipped forward vector realizes the target rate. -/
theorem binaryEndpointForwardClippedLevels_last_rate
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hsample :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointAwareAdjacentRate
        (binaryEndpointForwardClippedLevels sampleRate r) sampleRate
        (lastAdjacentIndex : Fin (m + 1)) =
      r := by
  let levels : Fin (m + 2) → ℝ :=
    binaryEndpointForwardClippedLevels sampleRate r
  let last : Fin (m + 1) := lastAdjacentIndex
  let low : Fin (m + 2) := adjacentLowIndex last
  have hlevel : levels low =
      binaryEndpointLastLevelOfRate (sampleRate low) r := by
    dsimp [levels, low, last]
    simpa [binaryEndpointForwardClippedCap] using
      binaryEndpointForwardClippedLevels_last_low hm sampleRate r
  have hrate :
      sampleRate low *
          (-Real.log (binaryEndpointLastLevelOfRate (sampleRate low) r)) =
        r :=
    binaryEndpointLastLevelOfRate_realizes hsample
  calc
    binaryEndpointAwareAdjacentRate levels sampleRate last =
        sampleRate low * (-Real.log (levels low)) := by
          simpa [last, low] using
            binaryEndpointAwareAdjacentRate_last
              levels sampleRate last
              (by simp [last, Nat.ne_of_gt hm])
              (by simp [last])
    _ = sampleRate low *
        (-Real.log (binaryEndpointLastLevelOfRate (sampleRate low) r)) := by
          rw [hlevel]
    _ = r := hrate

/-- The first adjacent levels of the clipped forward vector are strictly ordered. -/
theorem binaryEndpointForwardClippedLevels_first_adjacent_order
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hsample :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointForwardClippedLevels sampleRate r
        (adjacentLowIndex (firstAdjacentIndex : Fin (m + 1))) <
      binaryEndpointForwardClippedLevels sampleRate r
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  have hlow :
      binaryEndpointForwardClippedLevels sampleRate r
          (adjacentLowIndex (firstAdjacentIndex : Fin (m + 1))) = 0 := by
    simpa [firstAdjacentIndex, adjacentLowIndex] using
      binaryEndpointForwardClippedLevels_first sampleRate r
  have hhigh :
      binaryEndpointForwardClippedLevels sampleRate r
          (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) =
        binaryEndpointFirstLevelOfRate
          (sampleRate
            (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) r :=
    binaryEndpointForwardClippedLevels_first_high hm sampleRate r
  have hmem :
      binaryEndpointFirstLevelOfRate
          (sampleRate
            (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) r ∈
        Set.Ioo (0 : ℝ) 1 :=
    binaryEndpointFirstLevelOfRate_mem_Ioo hsample hr
  rw [hlow, hhigh]
  exact hmem.1

/-- The last adjacent levels of the clipped forward vector are strictly ordered. -/
theorem binaryEndpointForwardClippedLevels_last_adjacent_order
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hsample :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :
    binaryEndpointForwardClippedLevels sampleRate r
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
      binaryEndpointForwardClippedLevels sampleRate r
        (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) := by
  have hlow :
      binaryEndpointForwardClippedLevels sampleRate r
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
        binaryEndpointLastLevelOfRate
          (sampleRate
            (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) r := by
    simpa [binaryEndpointForwardClippedCap] using
      binaryEndpointForwardClippedLevels_last_low hm sampleRate r
  have hhigh :
      binaryEndpointForwardClippedLevels sampleRate r
          (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) = 1 := by
    have hidx :
        adjacentHighIndex (lastAdjacentIndex : Fin (m + 1)) =
          (lastLevelIndex : Fin (m + 2)) := by
      ext
      simp [adjacentHighIndex, lastAdjacentIndex]
    simpa [hidx] using binaryEndpointForwardClippedLevels_last sampleRate r
  have hmem :
      binaryEndpointLastLevelOfRate
          (sampleRate
            (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) r ∈
        Set.Ioo (0 : ℝ) 1 :=
    binaryEndpointLastLevelOfRate_mem_Ioo hsample hr
  rw [hlow, hhigh]
  exact hmem.2

/--
One interior step of the forward clipped cascade realizes the target rate
whenever the high-endpoint selector is genuinely feasible before the cap.
-/
theorem binaryEndpointForwardClippedLevelNat_step_rate_of_feasible {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (cap r : ℝ) (n : ℕ)
    (hfeasible :
      WeightedBernoulliHighEndpointTargetFeasible
        (binaryEndpointSampleRateNat sampleRate (n + 2))
        (binaryEndpointSampleRateNat sampleRate (n + 1))
        (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1))
        cap r) :
    weightedBernoulliClosedThresholdRate
        (binaryEndpointSampleRateNat sampleRate (n + 2))
        (binaryEndpointSampleRateNat sampleRate (n + 1))
        (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 2))
        (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1)) =
      r := by
  simpa [binaryEndpointForwardClippedLevelNat] using
    weightedBernoulliHighEndpointOfRateOrCap_rate_of_feasible hfeasible

/--
Nonterminal interior adjacent rates of the forward clipped vector realize the
target whenever the corresponding clipped-selector step is feasible.
-/
theorem binaryEndpointForwardClippedLevels_interior_step_rate_of_feasible
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) (n : ℕ)
    (hn : n + 2 < m)
    (hfeasible :
      WeightedBernoulliHighEndpointTargetFeasible
        (binaryEndpointSampleRateNat sampleRate (n + 2))
        (binaryEndpointSampleRateNat sampleRate (n + 1))
        (binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
        (binaryEndpointForwardClippedCap sampleRate r) r) :
    binaryEndpointAwareAdjacentRate
        (binaryEndpointForwardClippedLevels sampleRate r) sampleRate
        (⟨n + 1, by omega⟩ : Fin (m + 1)) =
      r := by
  let cap : ℝ := binaryEndpointForwardClippedCap sampleRate r
  let levels : Fin (m + 2) → ℝ :=
    binaryEndpointForwardClippedLevels sampleRate r
  let i : Fin (m + 1) := ⟨n + 1, by omega⟩
  have hlow_val_lt : (adjacentLowIndex i).val < m := by
    dsimp [i, adjacentLowIndex]
    omega
  have hhigh_val_lt : (adjacentHighIndex i).val < m := by
    dsimp [i, adjacentHighIndex]
    omega
  have hlow :
      levels (adjacentLowIndex i) =
        binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1) := by
    dsimp [levels, cap]
    have h :=
      binaryEndpointForwardClippedLevels_eq_levelNat_of_val_lt_m
        sampleRate r (adjacentLowIndex i) hlow_val_lt
    simpa [i, adjacentLowIndex] using h
  have hhigh :
      levels (adjacentHighIndex i) =
        binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 2) := by
    dsimp [levels, cap]
    have h :=
      binaryEndpointForwardClippedLevels_eq_levelNat_of_val_lt_m
        sampleRate r (adjacentHighIndex i) hhigh_val_lt
    simpa [i, adjacentHighIndex] using h
  have hrateNat :
      weightedBernoulliClosedThresholdRate
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 2))
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1)) =
        r := by
    dsimp [cap]
    exact
      binaryEndpointForwardClippedLevelNat_step_rate_of_feasible
        sampleRate (binaryEndpointForwardClippedCap sampleRate r) r n
        hfeasible
  have hn2_lt_m2 : n + 2 < m + 2 := by omega
  have hn1_lt_m2 : n + 1 < m + 2 := by omega
  have hrateNat' :
      weightedBernoulliClosedThresholdRate
          (sampleRate ⟨n + 2, hn2_lt_m2⟩)
          (sampleRate ⟨n + 1, hn1_lt_m2⟩)
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 2))
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1)) =
        r := by
    simpa [binaryEndpointSampleRateNat, hn2_lt_m2, hn1_lt_m2] using
      hrateNat
  have hi_first : i.val ≠ 0 := by
    dsimp [i]
    omega
  have hi_last : i.val ≠ m := by
    dsimp [i]
    omega
  calc
    binaryEndpointAwareAdjacentRate levels sampleRate i =
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (levels (adjacentHighIndex i))
          (levels (adjacentLowIndex i)) := by
      simpa using
        binaryEndpointAwareAdjacentRate_interior
          levels sampleRate i hi_first hi_last
    _ =
        weightedBernoulliClosedThresholdRate
          (sampleRate ⟨n + 2, hn2_lt_m2⟩)
          (sampleRate ⟨n + 1, hn1_lt_m2⟩)
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 2))
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1)) := by
      rw [hhigh, hlow]
      simp [i, adjacentLowIndex, adjacentHighIndex]
    _ = r := hrateNat'

/--
Nonterminal interior adjacent coordinates of the clipped vector are strictly
ordered whenever the corresponding clipped-selector step is feasible.
-/
theorem binaryEndpointForwardClippedLevels_interior_step_order_of_feasible
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ) (n : ℕ)
    (hn : n + 2 < m)
    (hfeasible :
      WeightedBernoulliHighEndpointTargetFeasible
        (binaryEndpointSampleRateNat sampleRate (n + 2))
        (binaryEndpointSampleRateNat sampleRate (n + 1))
        (binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
        (binaryEndpointForwardClippedCap sampleRate r) r) :
    binaryEndpointForwardClippedLevels sampleRate r
        (adjacentLowIndex (⟨n + 1, by omega⟩ : Fin (m + 1))) <
      binaryEndpointForwardClippedLevels sampleRate r
        (adjacentHighIndex (⟨n + 1, by omega⟩ : Fin (m + 1))) := by
  let cap : ℝ := binaryEndpointForwardClippedCap sampleRate r
  let i : Fin (m + 1) := ⟨n + 1, by omega⟩
  have hlow_val_lt : (adjacentLowIndex i).val < m := by
    dsimp [i, adjacentLowIndex]
    omega
  have hhigh_val_lt : (adjacentHighIndex i).val < m := by
    dsimp [i, adjacentHighIndex]
    omega
  have hlow :
      binaryEndpointForwardClippedLevels sampleRate r (adjacentLowIndex i) =
        binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1) := by
    dsimp [cap]
    have h :=
      binaryEndpointForwardClippedLevels_eq_levelNat_of_val_lt_m
        sampleRate r (adjacentLowIndex i) hlow_val_lt
    simpa [i, adjacentLowIndex] using h
  have hhigh :
      binaryEndpointForwardClippedLevels sampleRate r (adjacentHighIndex i) =
        binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 2) := by
    dsimp [cap]
    have h :=
      binaryEndpointForwardClippedLevels_eq_levelNat_of_val_lt_m
        sampleRate r (adjacentHighIndex i) hhigh_val_lt
    simpa [i, adjacentHighIndex] using h
  have hmem :
      binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 2) ∈
        Set.Ioo
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (n + 1))
          cap := by
    dsimp [cap]
    simpa [binaryEndpointForwardClippedLevelNat] using
      weightedBernoulliHighEndpointOfRateOrCap_mem_Ioo_of_feasible
        hfeasible
  have htarget :
      binaryEndpointForwardClippedLevels sampleRate r (adjacentLowIndex i) <
        binaryEndpointForwardClippedLevels sampleRate r (adjacentHighIndex i) := by
    rw [hlow, hhigh]
    exact hmem.1
  simpa [i, adjacentLowIndex, adjacentHighIndex] using htarget

/--
The terminal interior adjacent rate realizes the target whenever the forward
cascade terminal gap is zero.
-/
theorem binaryEndpointForwardClippedLevels_terminal_rate_of_gap_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    binaryEndpointAwareAdjacentRate
        (binaryEndpointForwardClippedLevels sampleRate r) sampleRate
        (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      r := by
  let cap : ℝ := binaryEndpointForwardClippedCap sampleRate r
  let levels : Fin (m + 2) → ℝ :=
    binaryEndpointForwardClippedLevels sampleRate r
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hm_sub_add : m - 1 + 1 = m := by omega
  have hlow_val_lt : (adjacentLowIndex i).val < m := by
    dsimp [i, adjacentLowIndex]
    omega
  have hlow :
      levels (adjacentLowIndex i) =
        binaryEndpointForwardClippedLevelNat sampleRate cap r (m - 1) := by
    dsimp [levels, cap]
    have h :=
      binaryEndpointForwardClippedLevels_eq_levelNat_of_val_lt_m
        sampleRate r (adjacentLowIndex i) hlow_val_lt
    simpa [i, adjacentLowIndex] using h
  have hhigh :
      levels (adjacentHighIndex i) = cap := by
    dsimp [levels, cap]
    have hcap :=
      binaryEndpointForwardClippedLevels_last_low
        (show 0 < m by omega) sampleRate r
    have hidx :
        adjacentHighIndex i =
          adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)) := by
      ext
      simp [i, adjacentHighIndex, lastAdjacentIndex, adjacentLowIndex,
        hm_sub_add]
    simpa [hidx] using hcap
  have hm_lt_m2 : m < m + 2 := by omega
  have hm1_lt_m2 : m - 1 < m + 2 := by omega
  have hterminal :
      weightedBernoulliClosedThresholdRate
          (sampleRate ⟨m, hm_lt_m2⟩)
          (sampleRate ⟨m - 1, hm1_lt_m2⟩)
          cap
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (m - 1)) =
        r := by
    have hgap' :
        weightedBernoulliClosedThresholdRate
            (binaryEndpointSampleRateNat sampleRate m)
            (binaryEndpointSampleRateNat sampleRate (m - 1))
            (binaryEndpointForwardClippedCap sampleRate r)
            (binaryEndpointForwardClippedLevelNat sampleRate
              (binaryEndpointForwardClippedCap sampleRate r) r (m - 1)) -
          r = 0 := by
      simpa [binaryEndpointForwardClippedTerminalGap,
        binaryEndpointForwardClippedTerminalRate,
        binaryEndpointForwardClippedPenultimateLevel] using hgap
    have hrate_eq :
        weightedBernoulliClosedThresholdRate
            (binaryEndpointSampleRateNat sampleRate m)
            (binaryEndpointSampleRateNat sampleRate (m - 1))
            (binaryEndpointForwardClippedCap sampleRate r)
            (binaryEndpointForwardClippedLevelNat sampleRate
              (binaryEndpointForwardClippedCap sampleRate r) r (m - 1)) =
          r := by
      linarith
    simpa [binaryEndpointSampleRateNat, hm_lt_m2, hm1_lt_m2, cap] using
      hrate_eq
  have hi_first : i.val ≠ 0 := by
    dsimp [i]
    omega
  have hi_last : i.val ≠ m := by
    dsimp [i]
    omega
  calc
    binaryEndpointAwareAdjacentRate levels sampleRate i =
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (levels (adjacentHighIndex i))
          (levels (adjacentLowIndex i)) := by
      simpa using
        binaryEndpointAwareAdjacentRate_interior
          levels sampleRate i hi_first hi_last
    _ =
        weightedBernoulliClosedThresholdRate
          (sampleRate ⟨m, hm_lt_m2⟩)
          (sampleRate ⟨m - 1, hm1_lt_m2⟩)
          cap
          (binaryEndpointForwardClippedLevelNat sampleRate cap r (m - 1)) := by
      rw [hhigh, hlow]
      simp [i, adjacentLowIndex, adjacentHighIndex, hm_sub_add]
    _ = r := hterminal

/--
The terminal interior adjacent coordinates are strictly ordered when the
penultimate forward-cascade level lies below the last endpoint-inverse cap.
-/
theorem binaryEndpointForwardClippedLevels_terminal_adjacent_order_of_lt_cap
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hterminal :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
        binaryEndpointForwardClippedCap sampleRate r) :
    binaryEndpointForwardClippedLevels sampleRate r
        (adjacentLowIndex (⟨m - 1, by omega⟩ : Fin (m + 1))) <
      binaryEndpointForwardClippedLevels sampleRate r
        (adjacentHighIndex (⟨m - 1, by omega⟩ : Fin (m + 1))) := by
  let cap : ℝ := binaryEndpointForwardClippedCap sampleRate r
  let i : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hm_sub_add : m - 1 + 1 = m := by omega
  have hlow_val_lt : (adjacentLowIndex i).val < m := by
    dsimp [i, adjacentLowIndex]
    omega
  have hlow :
      binaryEndpointForwardClippedLevels sampleRate r (adjacentLowIndex i) =
        binaryEndpointForwardClippedLevelNat sampleRate cap r (m - 1) := by
    dsimp [cap]
    have h :=
      binaryEndpointForwardClippedLevels_eq_levelNat_of_val_lt_m
        sampleRate r (adjacentLowIndex i) hlow_val_lt
    simpa [i, adjacentLowIndex] using h
  have hhigh :
      binaryEndpointForwardClippedLevels sampleRate r (adjacentHighIndex i) =
        cap := by
    dsimp [cap]
    have hcap :=
      binaryEndpointForwardClippedLevels_last_low
        (show 0 < m by omega) sampleRate r
    have hidx :
        adjacentHighIndex i =
          adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)) := by
      ext
      simp [i, adjacentHighIndex, lastAdjacentIndex, adjacentLowIndex,
        hm_sub_add]
    simpa [hidx] using hcap
  have htarget :
      binaryEndpointForwardClippedLevels sampleRate r (adjacentLowIndex i) <
        binaryEndpointForwardClippedLevels sampleRate r (adjacentHighIndex i) := by
    rw [hlow, hhigh]
    simpa [cap] using hterminal
  simpa [i, adjacentLowIndex, adjacentHighIndex, hm_sub_add] using htarget

/--
If every nonterminal clipped step is feasible and the terminal scalar gap is
zero, then all adjacent rates of the forward clipped vector equal the target
rate.
-/
theorem binaryEndpointForwardClippedLevels_all_rates_eq_of_feasible_and_gap_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    ∀ i : Fin (m + 1),
      binaryEndpointAwareAdjacentRate
          (binaryEndpointForwardClippedLevels sampleRate r) sampleRate i =
        r := by
  intro i
  by_cases hfirst : i.val = 0
  · have hi : i = (firstAdjacentIndex : Fin (m + 1)) := by
      ext
      simpa [firstAdjacentIndex] using hfirst
    simpa [hi] using
      binaryEndpointForwardClippedLevels_first_rate
        hm sampleRate r
        (hsample_high (firstAdjacentIndex : Fin (m + 1)))
  · by_cases hlast : i.val = m
    · have hi : i = (lastAdjacentIndex : Fin (m + 1)) := by
        ext
        simpa [lastAdjacentIndex] using hlast
      simpa [hi] using
        binaryEndpointForwardClippedLevels_last_rate
          (show 0 < m by omega) sampleRate r
          (hsample_low (lastAdjacentIndex : Fin (m + 1)))
    · by_cases hterminal : i.val = m - 1
      · have hi : i = (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
          ext
          simpa using hterminal
        simpa [hi] using
          binaryEndpointForwardClippedLevels_terminal_rate_of_gap_zero
            hm sampleRate r hgap
      · rcases Nat.exists_eq_succ_of_ne_zero hfirst with ⟨n, hn⟩
        have hn_step : n + 2 < m := by
          have hi_le : i.val ≤ m := Nat.le_of_lt_succ i.isLt
          omega
        have hi : i = (⟨n + 1, by omega⟩ : Fin (m + 1)) := by
          ext
          simpa [hn]
        simpa [hi] using
          binaryEndpointForwardClippedLevels_interior_step_rate_of_feasible
            sampleRate r n hn_step (hfeasible n hn_step)

/--
Forward clipped cascade equalization certificate: if the nonterminal steps are
feasible and the terminal scalar gap is zero, the clipped vector pairwise
equalizes all adjacent rates.
-/
theorem binaryEndpointForwardClippedLevels_equalizes_of_feasible_and_gap_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    BinaryEndpointAwareAdjacentRatesEqualize
      (binaryEndpointForwardClippedLevels sampleRate r) sampleRate := by
  have hall :=
    binaryEndpointForwardClippedLevels_all_rates_eq_of_feasible_and_gap_zero
      hm sampleRate r hsample_high hsample_low hfeasible hgap
  intro i j
  rw [hall i, hall j]

/--
Endpoint-vector feasibility for the forward clipped cascade from feasible
nonterminal steps and terminal order.
-/
theorem binaryEndpointForwardClippedLevels_isEndpointLevelVector
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hterminal :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
        binaryEndpointForwardClippedCap sampleRate r) :
    BinaryEndpointLevelVector (binaryEndpointForwardClippedLevels sampleRate r) := by
  constructor
  · exact binaryEndpointForwardClippedLevels_first sampleRate r
  constructor
  · exact binaryEndpointForwardClippedLevels_last sampleRate r
  · intro i
    by_cases hfirst : i.val = 0
    · have hi : i = (firstAdjacentIndex : Fin (m + 1)) := by
        ext
        simpa [firstAdjacentIndex] using hfirst
      simpa [hi] using
        binaryEndpointForwardClippedLevels_first_adjacent_order
          hm sampleRate hr
          (hsample_high (firstAdjacentIndex : Fin (m + 1)))
    · by_cases hlast : i.val = m
      · have hi : i = (lastAdjacentIndex : Fin (m + 1)) := by
          ext
          simpa [lastAdjacentIndex] using hlast
        simpa [hi] using
          binaryEndpointForwardClippedLevels_last_adjacent_order
            (show 0 < m by omega) sampleRate hr
            (hsample_low (lastAdjacentIndex : Fin (m + 1)))
      · by_cases hterm : i.val = m - 1
        · have hi : i = (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
            ext
            simpa using hterm
          simpa [hi] using
            binaryEndpointForwardClippedLevels_terminal_adjacent_order_of_lt_cap
              hm sampleRate r hterminal
        · rcases Nat.exists_eq_succ_of_ne_zero hfirst with ⟨n, hn⟩
          have hn_step : n + 2 < m := by
            have hi_le : i.val ≤ m := Nat.le_of_lt_succ i.isLt
            omega
          have hi : i = (⟨n + 1, by omega⟩ : Fin (m + 1)) := by
            ext
            simpa [hn]
          simpa [hi] using
            binaryEndpointForwardClippedLevels_interior_step_order_of_feasible
              sampleRate r n hn_step (hfeasible n hn_step)

/--
Conditional finite Lemma 3.1 existence from a scalar forward-cascade
certificate.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_exists_of_forward_clipped_certificate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hlevels :
      BinaryEndpointLevelVector (binaryEndpointForwardClippedLevels sampleRate r))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    ∃ levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  exact
    ⟨binaryEndpointForwardClippedLevels sampleRate r, hlevels,
      binaryEndpointForwardClippedLevels_equalizes_of_feasible_and_gap_zero
        hm sampleRate r hsample_high hsample_low hfeasible hgap⟩

/--
Conditional finite Lemma 3.1 existence from a scalar forward-cascade
certificate, with endpoint-vector feasibility derived from terminal order.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_exists_of_forward_clipped_scalar_certificate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hterminal :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
        binaryEndpointForwardClippedCap sampleRate r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    ∃ levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  exact
    binaryEndpointAwareAdjacentRatesEqualize_exists_of_forward_clipped_certificate
      hm sampleRate r hsample_high hsample_low
      (binaryEndpointForwardClippedLevels_isEndpointLevelVector
        hm sampleRate hr hsample_high hsample_low hfeasible hterminal)
      hfeasible hgap

/--
Interior next-level shooting for the endpoint-aware system: for a fixed low
level and positive target rate below the rate at a right cap, there is a unique
interior high level realizing that target rate.
-/
theorem exists_binaryEndpointInteriorHighLevelOfRate
    {gHi gLo pLo right target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_right : pLo < right)
    (hright1 : right < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_right :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo right pLo) :
    ∃ pHi : ℝ, pHi ∈ Set.Ioo pLo right ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target ∧
      (∀ x ∈ Set.Icc pLo right,
        weightedBernoulliClosedThresholdRate gHi gLo x pLo < target ↔
          x < pHi) ∧
      (∀ x ∈ Set.Icc pLo right,
        target < weightedBernoulliClosedThresholdRate gHi gLo x pLo ↔
          pHi < x) ∧
      (∀ x ∈ Set.Icc pLo right,
        weightedBernoulliClosedThresholdRate gHi gLo x pLo ≤ target ↔
          x ≤ pHi) ∧
      (∀ x ∈ Set.Icc pLo right,
        target ≤ weightedBernoulliClosedThresholdRate gHi gLo x pLo ↔
          pHi ≤ x) :=
  exists_high_endpoint_for_weightedBernoulliClosedThresholdRate
    hgHi hgLo hpLo0 hpLo_lt_right hright1 htarget_pos htarget_lt_right

/-- The interior high level realizing a target endpoint-aware rate is unique. -/
theorem existsUnique_binaryEndpointInteriorHighLevelOfRate
    {gHi gLo pLo right target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_right : pLo < right)
    (hright1 : right < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_right :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo right pLo) :
    ∃! pHi : ℝ, pHi ∈ Set.Ioo pLo right ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target :=
  existsUnique_high_endpoint_for_weightedBernoulliClosedThresholdRate
    hgHi hgLo hpLo0 hpLo_lt_right hright1 htarget_pos htarget_lt_right

/--
Interior previous-level shooting for the endpoint-aware system: for a fixed
high level and positive target rate below the rate at a left cap, there is a
unique interior low level realizing that target rate.
-/
theorem exists_binaryEndpointInteriorLowLevelOfRate
    {gHi gLo left pHi target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hleft0 : 0 < left) (hleft_lt_hi : left < pHi)
    (hpHi1 : pHi < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_left :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo pHi left) :
    ∃ pLo : ℝ, pLo ∈ Set.Ioo left pHi ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target ∧
      (∀ x ∈ Set.Icc left pHi,
        target < weightedBernoulliClosedThresholdRate gHi gLo pHi x ↔
          x < pLo) ∧
      (∀ x ∈ Set.Icc left pHi,
        weightedBernoulliClosedThresholdRate gHi gLo pHi x < target ↔
          pLo < x) ∧
      (∀ x ∈ Set.Icc left pHi,
        target ≤ weightedBernoulliClosedThresholdRate gHi gLo pHi x ↔
          x ≤ pLo) ∧
      (∀ x ∈ Set.Icc left pHi,
        weightedBernoulliClosedThresholdRate gHi gLo pHi x ≤ target ↔
          pLo ≤ x) :=
  exists_low_endpoint_for_weightedBernoulliClosedThresholdRate
    hgHi hgLo hleft0 hleft_lt_hi hpHi1 htarget_pos htarget_lt_left

/-- The interior low level realizing a target endpoint-aware rate is unique. -/
theorem existsUnique_binaryEndpointInteriorLowLevelOfRate
    {gHi gLo left pHi target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hleft0 : 0 < left) (hleft_lt_hi : left < pHi)
    (hpHi1 : pHi < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_left :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo pHi left) :
    ∃! pLo : ℝ, pLo ∈ Set.Ioo left pHi ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target :=
  existsUnique_low_endpoint_for_weightedBernoulliClosedThresholdRate
    hgHi hgLo hleft0 hleft_lt_hi hpHi1 htarget_pos htarget_lt_left

/-- Pairwise endpoint-aware equalization is equivalent to having a common rate. -/
theorem BinaryEndpointAwareAdjacentRatesEqualize.exists_common_rate {m : ℕ}
    {successProb sampleRate : Fin (m + 2) → ℝ}
    (h : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    ∃ r : ℝ, ∀ i : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate i = r := by
  refine
    ⟨binaryEndpointAwareAdjacentRate successProb sampleRate
      (firstAdjacentIndex : Fin (m + 1)), ?_⟩
  intro i
  exact h i (firstAdjacentIndex : Fin (m + 1))

/-- Equalized feasible endpoint-aware adjacent rates have a positive common value. -/
theorem BinaryEndpointAwareAdjacentRatesEqualize.exists_pos_common_rate {m : ℕ}
    (hm : 0 < m)
    {successProb sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (h : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    ∃ r : ℝ, 0 < r ∧ ∀ i : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate i = r := by
  rcases h.exists_common_rate with ⟨r, hr⟩
  have hr_pos :
      0 < r := by
    have hpos :=
      binaryEndpointAwareAdjacentRate_pos
        hm successProb sampleRate hlevels hsample_high hsample_low
        (firstAdjacentIndex : Fin (m + 1))
    rw [hr (firstAdjacentIndex : Fin (m + 1))] at hpos
    exact hpos
  exact ⟨r, hr_pos, hr⟩

/-- Finite objective that takes the worst closed adjacent binary rate. -/
def binaryClosedAdjacentRateObjective {m : ℕ}
    (g t : Fin (m + 2) → ℝ) : ℝ :=
  sInf (Set.range fun i : Fin (m + 1) =>
    binaryClosedAdjacentRateAt g t i)

/-- The finite adjacent closed rates equalize to one common value. -/
def BinaryClosedAdjacentRatesEqualize {m : ℕ}
    (g t : Fin (m + 2) → ℝ) : Prop :=
  ∀ i j : Fin (m + 1),
    binaryClosedAdjacentRateAt g t i =
      binaryClosedAdjacentRateAt g t j

/-- Source finite binary-rating model from success probabilities. -/
abbrev binaryRatingModel {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1) :
    FiniteRatingLDPModel Seller Bool :=
  realBinaryRatingLDPModel successProb hprob0 hprob1

theorem sourceBernoulliKL_eq_formula (a b : ℝ) :
    sourceBernoulliKL a b =
      a * Real.log (a / b) +
        (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  rfl

theorem sourceBernoulliKLTop_eq_source_formula (a b : ℝ) :
    sourceBernoulliKLTop a b =
      if 0 ≤ a ∧ a ≤ 1 then
        (sourceBernoulliKL a b : WithTop ℝ)
      else
        ⊤ := by
  rfl

theorem adjacentBinaryRatingRate_eq_source_formula
    (gHi gLo tHi tLo : ℝ) :
    adjacentBinaryRatingRate gHi gLo tHi tLo =
      sInf (Set.range fun a : ℝ =>
        gHi * sourceBernoulliKL a tHi +
          gLo * sourceBernoulliKL a tLo) := by
  rfl

theorem adjacentBinaryRatingRateTop_eq_source_formula
    (gHi gLo tHi tLo : ℝ) :
    adjacentBinaryRatingRateTop gHi gLo tHi tLo =
      sInf (Set.range fun a : ℝ =>
        withTopRealScale gHi (sourceBernoulliKLTop a tHi) +
          withTopRealScale gLo (sourceBernoulliKLTop a tLo)) := by
  rfl

theorem adjacentBinaryRatingClosedRateBase_eq_source_formula
    (gLo gHi tLo tHi : ℝ) :
    adjacentBinaryRatingClosedRateBase gLo gHi tLo tHi =
      ((1 - tLo) ^ (gLo / (gLo + gHi))) *
          ((1 - tHi) ^ (gHi / (gLo + gHi))) +
        (tLo ^ (gLo / (gLo + gHi))) *
          (tHi ^ (gHi / (gLo + gHi))) := by
  rfl

theorem adjacentBinaryRatingClosedRate_eq_source_formula
    (gLo gHi tLo tHi : ℝ) :
    adjacentBinaryRatingClosedRate gLo gHi tLo tHi =
      -(gLo + gHi) *
        Real.log
          (((1 - tLo) ^ (gLo / (gLo + gHi))) *
              ((1 - tHi) ^ (gHi / (gLo + gHi))) +
            (tLo ^ (gLo / (gLo + gHi))) *
              (tHi ^ (gHi / (gLo + gHi)))) := by
  rfl

/--
At the weighted geometric common threshold, the adjacent two-Bernoulli KL
objective has the paper's closed logarithmic value.
-/
theorem adjacentBinaryThresholdRate_weightedCommonThreshold_eq_closedRate
    {gLo gHi tLo tHi : ℝ} (hG : gHi + gLo ≠ 0)
    (htLo0 : 0 < tLo) (htLo1 : tLo < 1)
    (htHi0 : 0 < tHi) (htHi1 : tHi < 1) :
    twoBernoulliThresholdRate gHi gLo tHi tLo
        (weightedBernoulliCommonThreshold gHi gLo tHi tLo) =
      adjacentBinaryRatingClosedRate gLo gHi tLo tHi := by
  rw [twoBernoulliThresholdRate_weightedCommonThreshold_eq_closed
    hG htHi0 htHi1 htLo0 htLo1]
  unfold weightedBernoulliClosedThresholdRate weightedBernoulliClosedRateBase
    weightedBernoulliFailureBase weightedBernoulliSuccessBase
    adjacentBinaryRatingClosedRate adjacentBinaryRatingClosedRateBase
  ring_nf

/--
If all adjacent closed binary rates in a finite chain equal `r`, then the
finite worst-adjacent objective is exactly `r`.
-/
theorem binaryClosedAdjacentRateObjective_eq_common_of_all_eq {m : ℕ}
    (g t : Fin (m + 2) → ℝ) (r : ℝ)
    (h : ∀ i : Fin (m + 1), binaryClosedAdjacentRateAt g t i = r) :
    binaryClosedAdjacentRateObjective g t = r := by
  unfold binaryClosedAdjacentRateObjective
  have hrange :
      Set.range (fun i : Fin (m + 1) =>
        binaryClosedAdjacentRateAt g t i) = ({r} : Set ℝ) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, rfl⟩
      simp [h i]
    · intro hx
      refine ⟨0, ?_⟩
      simp at hx
      simp [h (0 : Fin (m + 1)), hx]
  rw [hrange]
  simp

/--
Equalized adjacent closed rates realize the finite worst-adjacent objective at
any adjacent interval.
-/
theorem binaryClosedAdjacentRateObjective_eq_rate_of_equalizes {m : ℕ}
    (g t : Fin (m + 2) → ℝ)
    (h : BinaryClosedAdjacentRatesEqualize g t)
    (i : Fin (m + 1)) :
    binaryClosedAdjacentRateObjective g t =
      binaryClosedAdjacentRateAt g t i :=
  binaryClosedAdjacentRateObjective_eq_common_of_all_eq
    g t (binaryClosedAdjacentRateAt g t i) (fun j => h j i)

/--
If all endpoint-aware adjacent rates in a finite chain equal `r`, then the
finite worst-adjacent objective is exactly `r`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (h :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate i = r) :
    binaryEndpointAwareAdjacentRateObjective successProb sampleRate = r := by
  unfold binaryEndpointAwareAdjacentRateObjective
  exact
    AppliedModelingLib.finiteMin_eq_of_forall
      (binaryEndpointAwareAdjacentRate successProb sampleRate) r h

/--
Endpoint-aware equalized adjacent rates realize the finite worst-adjacent
objective at any adjacent interval.
-/
theorem binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (h : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate)
    (i : Fin (m + 1)) :
    binaryEndpointAwareAdjacentRateObjective successProb sampleRate =
      binaryEndpointAwareAdjacentRate successProb sampleRate i :=
  binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
    successProb sampleRate
    (binaryEndpointAwareAdjacentRate successProb sampleRate i)
    (fun j => h j i)

/--
For a uniform equalized endpoint chain, the squared largest adjacent
probability gap is bounded by the equalized worst-adjacent rate.
-/
theorem binaryEndpointAdjacentMaxWidth_sq_le_objective_of_uniform_equalized
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (binaryEndpointAdjacentMaxWidth levels) ^ 2 ≤
      binaryEndpointAwareAdjacentRateObjective levels
        (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  obtain ⟨i, hmax_eq⟩ :=
    AppliedModelingLib.exists_finiteMax_eq
      (fun i : Fin (m + 1) =>
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i))
  let width : ℝ :=
    levels (adjacentHighIndex i) - levels (adjacentLowIndex i)
  have hwidth_nonneg : 0 ≤ width := by
    dsimp [width]
    exact BinaryEndpointLevelVector_adjacent_width_nonneg hlevels i
  have hwidth_lt_one : width < 1 := by
    dsimp [width]
    exact BinaryEndpointLevelVector_adjacent_width_lt_one hm hlevels i
  have hwidth_sq_lt_one : width ^ 2 < 1 :=
    (sq_lt_one_iff₀ hwidth_nonneg).mpr hwidth_lt_one
  have hlog_lower :
      width ^ 2 ≤ -Real.log (1 - width ^ 2) :=
    AppliedModelingLib.Math.le_neg_log_one_sub (sq_nonneg width) hwidth_sq_lt_one
  have hrate_lower :
      -Real.log (1 - width ^ 2) ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) i := by
    simpa [width] using
      binaryEndpointAwareAdjacentRate_uniform_ge_neg_log_one_sub_width_sq
        hm hlevels i
  have hobj_eq :
      binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) i :=
    binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
      levels (fun _ : Fin (m + 2) => (1 : ℝ)) heq i
  calc
    (binaryEndpointAdjacentMaxWidth levels) ^ 2 = width ^ 2 := by
      simpa [binaryEndpointAdjacentMaxWidth, hmax_eq, width]
    _ ≤ -Real.log (1 - width ^ 2) := hlog_lower
    _ ≤ binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) i := hrate_lower
    _ = binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := hobj_eq.symm

/--
The explicit C.5 doubled chain has worst-adjacent rate at most one quarter of
the old uniform equalized worst-adjacent rate.
-/
theorem uniformDoubledEndpointLevels_objective_rate_le_one_fourth_old_objective
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤
      (1 / 4 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  let firstNew : Fin ((2 * m + 1) + 1) := firstAdjacentIndex
  let firstOld : Fin (m + 1) := firstAdjacentIndex
  have hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) :=
    uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hnew_obj :
      binaryEndpointAwareAdjacentRateObjective
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) firstNew :=
    binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
      (uniformDoubledEndpointLevels oldLevels)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) hnewEq firstNew
  have hold_obj :
      binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) firstOld :=
    binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
      oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdEq firstOld
  have hnew_rate :
      binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) firstNew =
        uniformDoubledEndpointRateTransform
          (binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) firstOld) := by
    simpa [firstNew, firstOld] using
      uniformDoubledEndpointLevels_adjacent_rate_eq_transform
        hm holdLevels firstNew
  calc
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        =
      uniformDoubledEndpointRateTransform
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) firstOld) := by
        rw [hnew_obj, hnew_rate]
    _ ≤
      binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) firstOld / 4 :=
        uniformDoubledEndpointRateTransform_le_one_fourth _
    _ =
      (1 / 4 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
        rw [hold_obj]
        ring

/--
Lemma C.7 objective-rate comparison in certificate form.  If a refined uniform
equalized chain has last interior level `(1 + sqrt t_last) / 2`, then its
equalized worst-adjacent rate is at least one fifth of the old equalized
worst-adjacent rate.
-/
theorem BinaryEndpointLevelVector_uniform_refined_objective_rate_ge_one_fifth
    {mOld mNew : ℕ} (hmOld : 0 < mOld) (hmNew : 0 < mNew)
    {oldLevels : Fin (mOld + 2) → ℝ}
    {newLevels : Fin (mNew + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hnewLevels : BinaryEndpointLevelVector newLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (mOld + 2) => (1 : ℝ)))
    (hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize newLevels
        (fun _ : Fin (mNew + 2) => (1 : ℝ)))
    (hrefined :
      newLevels (adjacentLowIndex (lastAdjacentIndex : Fin (mNew + 1))) =
        (1 +
          Real.sqrt
            (oldLevels
              (adjacentLowIndex (lastAdjacentIndex : Fin (mOld + 1))))) / 2) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (mOld + 2) => (1 : ℝ)) ≤
      binaryEndpointAwareAdjacentRateObjective newLevels
        (fun _ : Fin (mNew + 2) => (1 : ℝ)) := by
  have hold_obj :
      binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (mOld + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (mOld + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (mOld + 1)) :=
    binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
      oldLevels (fun _ : Fin (mOld + 2) => (1 : ℝ)) holdEq
      (lastAdjacentIndex : Fin (mOld + 1))
  have hnew_obj :
      binaryEndpointAwareAdjacentRateObjective newLevels
          (fun _ : Fin (mNew + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate newLevels
          (fun _ : Fin (mNew + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (mNew + 1)) :=
    binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
      newLevels (fun _ : Fin (mNew + 2) => (1 : ℝ)) hnewEq
      (lastAdjacentIndex : Fin (mNew + 1))
  have hnew_last :
      binaryEndpointAwareAdjacentRate newLevels
          (fun _ : Fin (mNew + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (mNew + 1)) =
        -Real.log
          (newLevels
            (adjacentLowIndex (lastAdjacentIndex : Fin (mNew + 1)))) := by
    have hlast :=
      binaryEndpointAwareAdjacentRate_uniform_last_eq_neg_log_one_sub_width
        hmNew hnewLevels
    have hhigh :
        newLevels (adjacentHighIndex (lastAdjacentIndex : Fin (mNew + 1))) =
          1 := by
      simpa [lastAdjacentIndex, adjacentHighIndex, lastLevelIndex] using
        hnewLevels.2.1
    rw [hlast, hhigh]
    ring_nf
  have hcore :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (mOld + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (mOld + 1)) ≤
        -Real.log
          (newLevels
            (adjacentLowIndex (lastAdjacentIndex : Fin (mNew + 1)))) := by
    exact
      BinaryEndpointLevelVector_uniform_refined_last_rate_ge_one_fifth
        hmOld holdLevels holdEq
        (refinedLastLow :=
          newLevels
            (adjacentLowIndex (lastAdjacentIndex : Fin (mNew + 1))))
        hrefined
  calc
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (mOld + 2) => (1 : ℝ))
        =
      (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (mOld + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (mOld + 1)) := by
          rw [hold_obj]
    _ ≤
        -Real.log
          (newLevels
            (adjacentLowIndex (lastAdjacentIndex : Fin (mNew + 1)))) :=
          hcore
    _ =
        binaryEndpointAwareAdjacentRate newLevels
          (fun _ : Fin (mNew + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (mNew + 1)) := by
          simpa using hnew_last.symm
    _ =
        binaryEndpointAwareAdjacentRateObjective newLevels
          (fun _ : Fin (mNew + 2) => (1 : ℝ)) := by
          simpa using hnew_obj.symm

/--
Lemma C.5/C.7/C.8 composition: once the doubled uniform chain is known to be
feasible and equalized, the first refined level is at least one half of the
C.7 lower bound on the refined objective rate.
-/
theorem uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hnewLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels))
    (hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)))
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1) :
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ≤
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
  let lower : ℝ :=
    (1 / 5 : ℝ) *
      binaryEndpointAwareAdjacentRateObjective oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))
  have hobj_pos :
      0 <
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    have hobj_eq :
        binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) =
          binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (m + 1)) :=
      binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
        oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdEq
        (firstAdjacentIndex : Fin (m + 1))
    rw [hobj_eq]
    exact
      binaryEndpointAwareAdjacentRate_pos
        hm oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdLevels
        (by intro i; norm_num)
        (by intro i; norm_num)
        (firstAdjacentIndex : Fin (m + 1))
  have hlower0 : 0 ≤ lower := by
    dsimp [lower]
    positivity
  have hlower1 : lower ≤ 1 := by
    dsimp [lower]
    exact hlower_le_one
  have hrefined_last :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        (1 +
          Real.sqrt
            (oldLevels
              (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))) / 2 := by
    simpa [bernoulliLastEndpointEqualSplit] using
      uniformDoubledEndpointLevels_last_odd hm oldLevels
  have hrate_lower :
      lower ≤
        binaryEndpointAwareAdjacentRateObjective
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    dsimp [lower]
    exact
      BinaryEndpointLevelVector_uniform_refined_objective_rate_ge_one_fifth
        hm (by omega) holdLevels hnewLevels holdEq hnewEq hrefined_last
  exact
    BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_objective_rate_lower
      (m := 2 * m + 1) (by omega) hnewLevels hnewEq
      hlower0 hlower1 hrate_lower

/--
Lemma C.5/C.7/C.8 composition with C.5 feasibility discharged by the explicit
doubled-chain construction.  The remaining input is the global equalization
certificate for the doubled chain.
-/
theorem uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective_of_equalized
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)))
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1) :
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ≤
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
  uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective
    hm holdLevels holdEq
    (uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels)
    hnewEq hlower_le_one

/--
Lemma C.7 objective-rate comparison specialized to the explicit C.5 doubled
chain, with doubled-chain feasibility and equalization derived internally.
-/
theorem uniformDoubledEndpointLevels_objective_rate_ge_one_fifth_old_objective_closed
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
  have hrefined_last :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        (1 +
          Real.sqrt
            (oldLevels
              (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))) / 2 := by
    simpa [bernoulliLastEndpointEqualSplit] using
      uniformDoubledEndpointLevels_last_odd hm oldLevels
  exact
    BinaryEndpointLevelVector_uniform_refined_objective_rate_ge_one_fifth
      hm (by omega) holdLevels
      (uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels)
      holdEq (uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq)
      hrefined_last

/--
Lemma C.5/C.7/C.8 composition with the C.5 doubled-chain certificates fully
derived from the old uniform equalized endpoint chain.
-/
theorem uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective_closed
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1) :
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ≤
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
  uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective_of_equalized
    hm holdLevels holdEq
    (uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq)
    hlower_le_one

/--
Source-shaped finite maximin certificate for Lemma 3.1. If a candidate level
vector equalizes all endpoint-aware adjacent rates at `r`, and every feasible
alternative has some adjacent rate at most `r`, then the candidate maximizes
the finite worst-adjacent rate over that feasible family.
-/
theorem binaryEndpointAwareAdjacentRateObjective_maximal_of_equalized_and_no_simultaneous_improvement
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (feasible : (Fin (m + 2) → ℝ) → Prop)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hno_improve :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        ∃ i : Fin (m + 1),
          binaryEndpointAwareAdjacentRate alt sampleRate i ≤ r) :
    ∀ alt : Fin (m + 2) → ℝ, feasible alt →
      binaryEndpointAwareAdjacentRateObjective alt sampleRate ≤
        binaryEndpointAwareAdjacentRateObjective candidate sampleRate := by
  simpa [binaryEndpointAwareAdjacentRateObjective] using
    AppliedModelingLib.finiteMin_maximal_of_equalized_and_exists_component_le
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRate levels sampleRate)
      feasible candidate heq hno_improve

/--
`IsMaximizerOn` form of the finite maximin certificate used in Lemma 3.1.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_no_simultaneous_improvement
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (feasible : (Fin (m + 2) → ℝ) → Prop)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : feasible candidate)
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hno_improve :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        ∃ i : Fin (m + 1),
          binaryEndpointAwareAdjacentRate alt sampleRate i ≤ r) :
    AppliedModelingLib.Optimization.IsMaximizerOn feasible
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  refine ⟨hcandidate, ?_⟩
  exact
    binaryEndpointAwareAdjacentRateObjective_maximal_of_equalized_and_no_simultaneous_improvement
      sampleRate feasible candidate heq hno_improve

/--
Finite-chain cascade form of the source's "one cannot increase all adjacent
rates simultaneously" argument.  The hypotheses isolate the monotonicity facts
still needed from the Bernoulli closed-rate formula.
-/
theorem binaryEndpointAwareAdjacentRate_exists_rate_le_of_cascade
    {m : ℕ} (hm : 0 < m)
    (sampleRate candidate alternative : Fin (m + 2) → ℝ) {r : ℝ}
    (hfirst :
      r < binaryEndpointAwareAdjacentRate alternative sampleRate
          (firstAdjacentIndex : Fin (m + 1)) →
        candidate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) <
          alternative (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hstep :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        candidate (adjacentLowIndex i) < alternative (adjacentLowIndex i) →
        r < binaryEndpointAwareAdjacentRate alternative sampleRate i →
        candidate (adjacentHighIndex i) < alternative (adjacentHighIndex i))
    (hlast :
      candidate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
          alternative (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) →
        binaryEndpointAwareAdjacentRate alternative sampleRate
          (lastAdjacentIndex : Fin (m + 1)) ≤ r) :
    ∃ i : Fin (m + 1),
      binaryEndpointAwareAdjacentRate alternative sampleRate i ≤ r := by
  let candidateNat : ℕ → ℝ := fun n =>
    if h : n < m + 2 then candidate ⟨n, h⟩ else 0
  let alternativeNat : ℕ → ℝ := fun n =>
    if h : n < m + 2 then alternative ⟨n, h⟩ else 0
  let rateNat : ℕ → ℝ := fun n =>
    if h : n < m + 1 then
      binaryEndpointAwareAdjacentRate alternative sampleRate ⟨n, h⟩
    else 0
  have hcascade :=
    AppliedModelingLib.exists_index_le_of_endpoint_cascade
      (m := m) hm
      (candidate := candidateNat) (alternative := alternativeNat)
      (rate := rateNat) (r := r)
      (by
        intro hrate
        have hrate' :
            r < binaryEndpointAwareAdjacentRate alternative sampleRate
              (firstAdjacentIndex : Fin (m + 1)) := by
          simpa [rateNat, firstAdjacentIndex] using hrate
        have hmove := hfirst hrate'
        simpa [candidateNat, alternativeNat, firstAdjacentIndex,
          adjacentHighIndex] using hmove)
      (by
        intro i hi1 him hcoord hrate
        let fi : Fin (m + 1) := ⟨i, by omega⟩
        have hi_lt_m2 : i < m + 2 := by omega
        have hi_lt_m1 : i < m + 1 := by omega
        have hi_le_m : i ≤ m := Nat.le_of_lt_succ hi_lt_m1
        have hi_succ_lt_m2 : i + 1 < m + 2 := by omega
        have hcoord' :
            candidate (adjacentLowIndex fi) < alternative (adjacentLowIndex fi) := by
          have hcoord_raw :
              candidate ⟨i, hi_lt_m2⟩ < alternative ⟨i, hi_lt_m2⟩ := by
            simpa [candidateNat, alternativeNat, hi_lt_m2] using hcoord
          simpa [fi, adjacentLowIndex] using hcoord_raw
        have hrate' :
            r < binaryEndpointAwareAdjacentRate alternative sampleRate
              fi := by
          have hrate_raw :
              r < binaryEndpointAwareAdjacentRate alternative sampleRate
                ⟨i, hi_lt_m1⟩ := by
            simpa [rateNat, hi_le_m] using hrate
          simpa [fi] using hrate_raw
        have hmove := hstep fi (by simpa [fi] using ne_of_gt hi1) (by
          intro hval
          have : i = m := by simpa [fi] using hval
          omega) hcoord' hrate'
        have hmove_raw :
            candidate ⟨i + 1, hi_succ_lt_m2⟩ <
              alternative ⟨i + 1, hi_succ_lt_m2⟩ := by
          simpa [fi, adjacentHighIndex] using hmove
        simpa [candidateNat, alternativeNat, hi_succ_lt_m2] using hmove_raw)
      (by
        intro hcoord
        have hm_lt_m2 : m < m + 2 := by omega
        have hcoord' :
            candidate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
              alternative (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
          have hcoord_raw :
              candidate ⟨m, hm_lt_m2⟩ < alternative ⟨m, hm_lt_m2⟩ := by
            simpa [candidateNat, alternativeNat, hm_lt_m2] using hcoord
          simpa [adjacentLowIndex, lastAdjacentIndex] using hcoord_raw
        have hlast' := hlast hcoord'
        simpa [rateNat, lastAdjacentIndex, Nat.lt_succ_self] using hlast')
  rcases hcascade with ⟨i, hi_le, hrate⟩
  have hi_lt_m1 : i < m + 1 := Nat.lt_succ_of_le hi_le
  refine ⟨⟨i, hi_lt_m1⟩, ?_⟩
  simpa [rateNat, hi_le] using hrate

/--
Endpoint-aware Lemma 3.1 maximin certificate in the source's cascade form.
Equalization gives the candidate value; the three cascade hypotheses show that
no feasible alternative can raise every adjacent rate above it.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_cascade
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (feasible : (Fin (m + 2) → ℝ) → Prop)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : feasible candidate)
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hfirst :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        r < binaryEndpointAwareAdjacentRate alt sampleRate
            (firstAdjacentIndex : Fin (m + 1)) →
          candidate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) <
            alt (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hstep :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          r < binaryEndpointAwareAdjacentRate alt sampleRate i →
          candidate (adjacentHighIndex i) < alt (adjacentHighIndex i))
    (hlast :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        candidate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
            alt (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) →
          binaryEndpointAwareAdjacentRate alt sampleRate
            (lastAdjacentIndex : Fin (m + 1)) ≤ r) :
    AppliedModelingLib.Optimization.IsMaximizerOn feasible
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  refine
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_no_simultaneous_improvement
      sampleRate feasible candidate hcandidate heq ?_
  intro alt halt
  exact
    binaryEndpointAwareAdjacentRate_exists_rate_le_of_cascade
      hm sampleRate candidate alt
      (hfirst alt halt)
      (hstep alt halt)
      (hlast alt halt)

/--
Endpoint-aware Lemma 3.1 maximin certificate with the endpoint monotonicity
steps discharged.  The only remaining cascade input is the interior
closed-rate monotonicity: moving level `i` upward and improving interval `i`
forces level `i+1` upward.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_cascade
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_first :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hsample_last :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hstep :
      ∀ alt : Fin (m + 2) → ℝ, BinaryEndpointLevelVector alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          r < binaryEndpointAwareAdjacentRate alt sampleRate i →
          candidate (adjacentHighIndex i) < alt (adjacentHighIndex i)) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  refine
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_cascade
      hm sampleRate
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      candidate hcandidate heq ?_ hstep ?_
  · intro alt halt hrate
    exact
      binaryEndpointAwareAdjacentRate_first_improvement_forces_high_increase
        hm sampleRate candidate alt hcandidate halt hsample_first
        (heq (firstAdjacentIndex : Fin (m + 1))) hrate
  · intro alt _halt hmove
    exact
      binaryEndpointAwareAdjacentRate_last_increase_blocks_rate_improvement
        hm sampleRate candidate alt hcandidate hsample_last
        (heq (lastAdjacentIndex : Fin (m + 1))) hmove

/--
Endpoint-aware Lemma 3.1 maximin certificate from the usual interior
monotonicity inequality.  For each interior interval, moving the lower endpoint
up while keeping the upper endpoint no higher cannot raise the adjacent rate
above the candidate's equalized value.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_monotone
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_first :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hsample_last :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hinterior_mono :
      ∀ alt : Fin (m + 2) → ℝ, BinaryEndpointLevelVector alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i) →
          binaryEndpointAwareAdjacentRate alt sampleRate i ≤ r) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  refine
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_cascade
      hm sampleRate candidate hcandidate hsample_first hsample_last heq ?_
  intro alt halt i hfirst hlast hlow hrate
  by_contra hnot
  have hhi_le : alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i) :=
    le_of_not_gt hnot
  exact not_lt_of_ge (hinterior_mono alt halt i hfirst hlast hlow hhi_le) hrate

/--
Endpoint-aware Lemma 3.1 maximin certificate from the closed-rate-base
comparison.  This is the algebraic target for the remaining Bernoulli
real-analysis proof: under interior endpoint moves that shrink the interval,
the closed-rate base must weakly increase.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_base_monotone
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_first :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hsample_last :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hsample_sum_nonneg :
      ∀ i : Fin (m + 1),
        0 ≤ sampleRate (adjacentHighIndex i) +
          sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hbase_mono :
      ∀ alt : Fin (m + 2) → ℝ, BinaryEndpointLevelVector alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i) →
          weightedBernoulliClosedRateBase
              (sampleRate (adjacentHighIndex i))
              (sampleRate (adjacentLowIndex i))
              (candidate (adjacentHighIndex i))
              (candidate (adjacentLowIndex i)) ≤
            weightedBernoulliClosedRateBase
              (sampleRate (adjacentHighIndex i))
              (sampleRate (adjacentLowIndex i))
              (alt (adjacentHighIndex i))
              (alt (adjacentLowIndex i))) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  refine
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_monotone
      hm sampleRate candidate hcandidate hsample_first hsample_last heq ?_
  intro alt halt i hfirst hlast hlow hhi_le
  have hhi_not_first : (adjacentHighIndex i).val ≠ 0 := by
    simp [adjacentHighIndex]
  have hhi_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
    simp [adjacentHighIndex]
    omega
  have hlo_not_last : (adjacentLowIndex i).val ≠ m + 1 := by
    simp [adjacentLowIndex]
    omega
  have hpHi0 : 0 < candidate (adjacentHighIndex i) :=
    BinaryEndpointLevelVector_pos_of_not_first hcandidate
      (adjacentHighIndex i) hhi_not_first
  have hpHi1 : candidate (adjacentHighIndex i) < 1 :=
    BinaryEndpointLevelVector_lt_one_of_not_last hcandidate
      (adjacentHighIndex i) hhi_not_last
  have hpLo0 : 0 < candidate (adjacentLowIndex i) :=
    BinaryEndpointLevelVector_pos_of_not_first hcandidate
      (adjacentLowIndex i) hfirst
  have hpLo1 : candidate (adjacentLowIndex i) < 1 :=
    BinaryEndpointLevelVector_lt_one_of_not_last hcandidate
      (adjacentLowIndex i) hlo_not_last
  have hbase_pos :
      0 < weightedBernoulliClosedRateBase
        (sampleRate (adjacentHighIndex i))
        (sampleRate (adjacentLowIndex i))
        (candidate (adjacentHighIndex i))
        (candidate (adjacentLowIndex i)) :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hclosed_le :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (alt (adjacentHighIndex i))
          (alt (adjacentLowIndex i)) ≤
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (candidate (adjacentHighIndex i))
          (candidate (adjacentLowIndex i)) :=
    weightedBernoulliClosedThresholdRate_le_of_closedRateBase_le
      (hsample_sum_nonneg i) hbase_pos
      (hbase_mono alt halt i hfirst hlast hlow hhi_le)
  have hcandidate_closed :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (candidate (adjacentHighIndex i))
          (candidate (adjacentLowIndex i)) = r :=
    (binaryEndpointAwareAdjacentRate_interior candidate sampleRate i
      hfirst hlast).symm.trans (heq i)
  have hclosed_le_r :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (alt (adjacentHighIndex i))
          (alt (adjacentLowIndex i)) ≤ r :=
    hclosed_le.trans_eq hcandidate_closed
  simpa [binaryEndpointAwareAdjacentRate_interior alt sampleRate i hfirst hlast]
    using hclosed_le_r

/--
Interior adjacent-rate strict monotonicity: if an alternative strictly moves
the lower endpoint up while keeping the upper endpoint no higher, then that
interior adjacent rate is strictly lower than the candidate's rate.
-/
theorem binaryEndpointAwareAdjacentRate_interior_lt_of_low_strict_shrink
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    (hsample_high : 0 < sampleRate (adjacentHighIndex i))
    (hsample_low : 0 < sampleRate (adjacentLowIndex i))
    (hlow : candidate (adjacentLowIndex i) < alt (adjacentLowIndex i))
    (hhi_le : alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i)) :
    binaryEndpointAwareAdjacentRate alt sampleRate i <
      binaryEndpointAwareAdjacentRate candidate sampleRate i := by
  have hhi_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
    simp [adjacentHighIndex]
    omega
  have hpLo0 : 0 < candidate (adjacentLowIndex i) :=
    BinaryEndpointLevelVector_pos_of_not_first hcandidate
      (adjacentLowIndex i) hfirst
  have hpHi1 : candidate (adjacentHighIndex i) < 1 :=
    BinaryEndpointLevelVector_lt_one_of_not_last hcandidate
      (adjacentHighIndex i) hhi_not_last
  have hclosed_lt :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (alt (adjacentHighIndex i))
          (alt (adjacentLowIndex i)) <
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (candidate (adjacentHighIndex i))
          (candidate (adjacentLowIndex i)) :=
    weightedBernoulliClosedThresholdRate_lt_of_shrink_lo_lt
      hsample_high hsample_low hpLo0 hlow (halt.2.2 i).le hhi_le hpHi1
  simpa [binaryEndpointAwareAdjacentRate_interior candidate sampleRate i hfirst hlast,
    binaryEndpointAwareAdjacentRate_interior alt sampleRate i hfirst hlast]
    using hclosed_lt

/--
Interior adjacent-rate strict monotonicity: if an alternative weakly moves the
lower endpoint up and strictly moves the upper endpoint down, then that
interior adjacent rate is strictly lower than the candidate's rate.
-/
theorem binaryEndpointAwareAdjacentRate_interior_lt_of_high_strict_shrink
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    (hsample_high : 0 < sampleRate (adjacentHighIndex i))
    (hsample_low : 0 < sampleRate (adjacentLowIndex i))
    (hlow_le : candidate (adjacentLowIndex i) ≤ alt (adjacentLowIndex i))
    (hhi_lt : alt (adjacentHighIndex i) < candidate (adjacentHighIndex i)) :
    binaryEndpointAwareAdjacentRate alt sampleRate i <
      binaryEndpointAwareAdjacentRate candidate sampleRate i := by
  have hhi_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
    simp [adjacentHighIndex]
    omega
  have hpLo0 : 0 < candidate (adjacentLowIndex i) :=
    BinaryEndpointLevelVector_pos_of_not_first hcandidate
      (adjacentLowIndex i) hfirst
  have hpHi1 : candidate (adjacentHighIndex i) < 1 :=
    BinaryEndpointLevelVector_lt_one_of_not_last hcandidate
      (adjacentHighIndex i) hhi_not_last
  have hclosed_lt :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (alt (adjacentHighIndex i))
          (alt (adjacentLowIndex i)) <
        weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (candidate (adjacentHighIndex i))
          (candidate (adjacentLowIndex i)) :=
    weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
      hsample_high hsample_low hpLo0 hlow_le (halt.2.2 i).le hhi_lt hpHi1
  simpa [binaryEndpointAwareAdjacentRate_interior candidate sampleRate i hfirst hlast,
    binaryEndpointAwareAdjacentRate_interior alt sampleRate i hfirst hlast]
    using hclosed_lt

/--
Interior adjacent-rate inverse monotonicity in the lower endpoint.  If an
alternative interval has high endpoint at least the candidate's and no larger
adjacent rate, then its low endpoint is at least the candidate's low endpoint.
-/
theorem binaryEndpointAwareAdjacentRate_interior_low_le_of_high_le_and_rate_le
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    (hsample_high : 0 < sampleRate (adjacentHighIndex i))
    (hsample_low : 0 < sampleRate (adjacentLowIndex i))
    (hhi_le :
      candidate (adjacentHighIndex i) ≤ alt (adjacentHighIndex i))
    (hrate_le :
      binaryEndpointAwareAdjacentRate alt sampleRate i ≤
        binaryEndpointAwareAdjacentRate candidate sampleRate i) :
    candidate (adjacentLowIndex i) ≤ alt (adjacentLowIndex i) := by
  by_contra hnot
  have hlow_lt :
      alt (adjacentLowIndex i) < candidate (adjacentLowIndex i) :=
    lt_of_not_ge hnot
  have hrate_lt :
      binaryEndpointAwareAdjacentRate candidate sampleRate i <
        binaryEndpointAwareAdjacentRate alt sampleRate i :=
    binaryEndpointAwareAdjacentRate_interior_lt_of_low_strict_shrink
      sampleRate alt candidate halt hcandidate i hfirst hlast
      hsample_high hsample_low hlow_lt hhi_le
  exact not_lt_of_ge hrate_le hrate_lt

/--
Interior adjacent-rate injectivity in the upper endpoint: when two feasible
level vectors agree on an interior interval's lower endpoint, equality of that
adjacent rate forces equality of the upper endpoint.
-/
theorem binaryEndpointAwareAdjacentRate_interior_high_eq_of_low_eq_and_rate_eq
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    (hsample_high : 0 < sampleRate (adjacentHighIndex i))
    (hsample_low : 0 < sampleRate (adjacentLowIndex i))
    (hlow_eq : candidate (adjacentLowIndex i) = alt (adjacentLowIndex i))
    (hrate :
      binaryEndpointAwareAdjacentRate candidate sampleRate i =
        binaryEndpointAwareAdjacentRate alt sampleRate i) :
    candidate (adjacentHighIndex i) = alt (adjacentHighIndex i) := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hrate_lt :
        binaryEndpointAwareAdjacentRate candidate sampleRate i <
          binaryEndpointAwareAdjacentRate alt sampleRate i :=
      binaryEndpointAwareAdjacentRate_interior_lt_of_high_strict_shrink
        sampleRate alt candidate halt hcandidate i hfirst hlast
        hsample_high hsample_low (le_of_eq hlow_eq.symm) hlt
    exact (not_lt_of_ge (le_of_eq hrate.symm)) hrate_lt
  · have hrate_lt :
        binaryEndpointAwareAdjacentRate alt sampleRate i <
          binaryEndpointAwareAdjacentRate candidate sampleRate i :=
      binaryEndpointAwareAdjacentRate_interior_lt_of_high_strict_shrink
        sampleRate candidate alt hcandidate halt i hfirst hlast
        hsample_high hsample_low (le_of_eq hlow_eq) hgt
    exact (not_lt_of_ge (le_of_eq hrate)) hrate_lt

/--
Endpoint-aware finite maximin theorem for the equalized Lemma 3.1 level
certificate.  For positive adjacent sample rates and endpoint-normalized
strictly increasing levels, equalized endpoint-aware adjacent rates maximize
the finite worst-adjacent closed rate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  refine
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_base_monotone
      hm sampleRate candidate hcandidate
      (hsample_high (firstAdjacentIndex : Fin (m + 1)))
      (hsample_low (lastAdjacentIndex : Fin (m + 1)))
      ?_ heq ?_
  · intro i
    exact add_nonneg (le_of_lt (hsample_high i)) (le_of_lt (hsample_low i))
  · intro alt halt i hfirst hlast hlow hhi_le
    have hlo_pos :
        0 < candidate (adjacentLowIndex i) :=
      BinaryEndpointLevelVector_pos_of_not_first hcandidate
        (adjacentLowIndex i) hfirst
    have hhi_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
      simp [adjacentHighIndex]
      omega
    have hhi_lt_one :
        candidate (adjacentHighIndex i) < 1 :=
      BinaryEndpointLevelVector_lt_one_of_not_last hcandidate
        (adjacentHighIndex i) hhi_not_last
    exact weightedBernoulliClosedRateBase_le_of_shrink
      (le_of_lt (hsample_high i)) (le_of_lt (hsample_low i))
      (add_pos (hsample_high i) (hsample_low i))
      hlo_pos hlow.le (halt.2.2 i).le hhi_le hhi_lt_one

/--
Source-shaped endpoint-aware finite maximin theorem for Lemma 3.1: pairwise
equalization of all adjacent rates supplies the common-rate certificate used by
the maximin proof.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  rcases heq.exists_common_rate with ⟨r, hr⟩
  exact
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized
      hm sampleRate candidate hcandidate hsample_high hsample_low hr

/--
Theorem 3.1 rate-optimality over the finite level problem: once the adjacent
rates are pairwise equalized, no endpoint-normalized alternative has a larger
worst-adjacent large-deviation rate.
-/
theorem theorem31_rate_optimal_of_pairwise_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    binaryEndpointAwareAdjacentRateObjective alt sampleRate ≤
      binaryEndpointAwareAdjacentRateObjective candidate sampleRate :=
  (binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized
    hm sampleRate candidate hcandidate hsample_high hsample_low heq).le halt

/--
Any uniform equalized finite optimum dominates the concrete uniformly spaced
endpoint chain, so it inherits the same polynomial objective lower bound.
-/
theorem BinaryEndpointAwareAdjacentRatesEqualize_uniform_objective_ge_inv_adjacent_count_sq
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (1 / ((m + 1 : ℕ) : ℝ)) ^ 2 ≤
      binaryEndpointAwareAdjacentRateObjective levels
        (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  have huniform_lower :=
    uniformEndpointLevels_objective_ge_inv_adjacent_count_sq (m := m) hm
  have hoptimal :
      binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m)
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ)) :=
    theorem31_rate_optimal_of_pairwise_equalized
      hm (fun _ : Fin (m + 2) => (1 : ℝ)) levels
      (uniformEndpointLevels m) hlevels
      (uniformEndpointLevels_isEndpointLevelVector m)
      (by intro i; norm_num) (by intro i; norm_num) heq
  exact huniform_lower.trans hoptimal

/--
Corollary C.3 finite lower-bound core for monotone match functions.  After
normalizing the first nonzero type rate to one, the uniformly spaced endpoint
chain has at least the uniform-sampling objective; rate optimality of the
equalized finite solution then gives the first-level polynomial lower bound.
-/
theorem BinaryEndpointAwareAdjacentRatesEqualize_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1) :
    ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
  let lower : ℝ := (1 / ((m + 1 : ℕ) : ℝ)) ^ 2
  have hsample_high : ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) :=
    fun i => hsample_pos (adjacentHighIndex i)
  have hsample_low : ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) :=
    fun i => hsample_pos (adjacentLowIndex i)
  have hmono_obj :
      binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m)
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
        binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m)
          sampleRate := by
    unfold binaryEndpointAwareAdjacentRateObjective
    refine AppliedModelingLib.le_finiteMin _ ?_
    intro i
    exact
      (AppliedModelingLib.finiteMin_le
        (binaryEndpointAwareAdjacentRate (uniformEndpointLevels m)
          (fun _ : Fin (m + 2) => (1 : ℝ))) i).trans
        (binaryEndpointAwareAdjacentRate_uniformEndpointLevels_le_of_sampleRate_mono_first_eq_one
          hm sampleRate hsample_pos hsample_mono hfirst_sample i)
  have hlower_uniform :
      lower ≤
        binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m)
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    simpa [lower] using uniformEndpointLevels_objective_ge_inv_adjacent_count_sq (m := m) hm
  have hlower_sample :
      lower ≤ binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m) sampleRate :=
    hlower_uniform.trans hmono_obj
  have hoptimal :
      binaryEndpointAwareAdjacentRateObjective (uniformEndpointLevels m) sampleRate ≤
        binaryEndpointAwareAdjacentRateObjective levels sampleRate :=
    theorem31_rate_optimal_of_pairwise_equalized
      hm sampleRate levels (uniformEndpointLevels m) hlevels
      (uniformEndpointLevels_isEndpointLevelVector m)
      hsample_high hsample_low heq
  have hlower_opt :
      lower ≤ binaryEndpointAwareAdjacentRateObjective levels sampleRate :=
    hlower_sample.trans hoptimal
  have hlower_first_sample :
      lower ≤ binaryEndpointAwareAdjacentRate levels sampleRate
          (firstAdjacentIndex : Fin (m + 1)) := by
    simpa [binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
      levels sampleRate heq (firstAdjacentIndex : Fin (m + 1))] using hlower_opt
  have hfirst_rate_eq :
      binaryEndpointAwareAdjacentRate levels sampleRate
          (firstAdjacentIndex : Fin (m + 1)) =
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (m + 1)) := by
    let first : Fin (m + 1) := firstAdjacentIndex
    let firstHigh : Fin (m + 2) := adjacentHighIndex first
    have hfirst_sample' : sampleRate firstHigh = 1 := by
      simpa [firstHigh, first] using hfirst_sample
    have hsample_formula :
        binaryEndpointAwareAdjacentRate levels sampleRate first =
          sampleRate firstHigh * (-Real.log (1 - levels firstHigh)) := by
      simpa [first, firstHigh] using
        binaryEndpointAwareAdjacentRate_first levels sampleRate first (by simp [first])
    have huniform_formula :
        binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ)) first =
          (1 : ℝ) * (-Real.log (1 - levels firstHigh)) := by
      simpa [first, firstHigh] using
        binaryEndpointAwareAdjacentRate_first
          levels (fun _ : Fin (m + 2) => (1 : ℝ)) first (by simp [first])
    rw [hsample_formula, huniform_formula, hfirst_sample']
  have hlower_first_uniform :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (m + 1)) := by
    calc
      lower ≤
          binaryEndpointAwareAdjacentRate levels sampleRate
            (firstAdjacentIndex : Fin (m + 1)) := hlower_first_sample
      _ =
          binaryEndpointAwareAdjacentRate levels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (m + 1)) := hfirst_rate_eq
  have hlower0 : 0 ≤ lower := by
    dsimp [lower]
    positivity
  have hlower1 : lower ≤ 1 := by
    dsimp [lower]
    have hden_ge_one : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
    have hinv_le_one :
        1 / ((m + 1 : ℕ) : ℝ) ≤ (1 : ℝ) := by
      have h :=
        one_div_le_one_div_of_le (a := (1 : ℝ))
          (b := ((m + 1 : ℕ) : ℝ)) zero_lt_one hden_ge_one
      simpa using h
    have hinv_nonneg : 0 ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
      positivity
    exact (sq_le_one_iff₀ hinv_nonneg).mpr hinv_le_one
  exact
    BinaryEndpointLevelVector_uniform_first_level_ge_half_of_first_rate_lower
      hm hlevels hlower0 hlower1 hlower_first_uniform

/--
Finite Lemma 3.1 uniqueness direction for equalized endpoint-aware level
vectors: two endpoint-normalized feasible level vectors that both equalize all
adjacent rates must be the same vector.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_unique
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq_candidate :
      BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate)
    (heq_alt :
      BinaryEndpointAwareAdjacentRatesEqualize alt sampleRate) :
    candidate = alt := by
  rcases heq_candidate.exists_common_rate with ⟨rc, hrc⟩
  rcases heq_alt.exists_common_rate with ⟨ra, hra⟩
  have hmax_candidate :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
        candidate :=
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized
      hm sampleRate candidate hcandidate hsample_high hsample_low hrc
  have hmax_alt :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
        alt :=
    binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized
      hm sampleRate alt halt hsample_high hsample_low hra
  have hobj_eq :
      binaryEndpointAwareAdjacentRateObjective candidate sampleRate =
        binaryEndpointAwareAdjacentRateObjective alt sampleRate :=
    AppliedModelingLib.Optimization.IsMaximizerOn.objective_eq_of_isMaximizerOn
      hmax_candidate hmax_alt
  have hobj_candidate :
      binaryEndpointAwareAdjacentRateObjective candidate sampleRate = rc :=
    binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
      candidate sampleRate rc hrc
  have hobj_alt :
      binaryEndpointAwareAdjacentRateObjective alt sampleRate = ra :=
    binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
      alt sampleRate ra hra
  have hrc_eq_ra : rc = ra := by
    rw [hobj_candidate, hobj_alt] at hobj_eq
    exact hobj_eq
  have hrate_eq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i =
          binaryEndpointAwareAdjacentRate alt sampleRate i := by
    intro i
    calc
      binaryEndpointAwareAdjacentRate candidate sampleRate i = rc := hrc i
      _ = ra := hrc_eq_ra
      _ = binaryEndpointAwareAdjacentRate alt sampleRate i := (hra i).symm
  have hcoord :
      ∀ k : ℕ, k ≤ m + 1 →
        ∀ hk : k < m + 2, candidate ⟨k, hk⟩ = alt ⟨k, hk⟩ := by
    intro k hk
    induction k with
    | zero =>
        intro hk0
        have hc0 : candidate (firstLevelIndex : Fin (m + 2)) = 0 := hcandidate.1
        have ha0 : alt (firstLevelIndex : Fin (m + 2)) = 0 := halt.1
        simpa [firstLevelIndex] using hc0.trans ha0.symm
    | succ k ih =>
        intro hksucc
        by_cases hlast_coord : k = m
        · subst k
          have hclast : candidate (lastLevelIndex : Fin (m + 2)) = 1 :=
            hcandidate.2.1
          have halast : alt (lastLevelIndex : Fin (m + 2)) = 1 :=
            halt.2.1
          simpa [lastLevelIndex] using hclast.trans halast.symm
        · have hk_lt_m : k < m := by omega
          have hk_lt_adj : k < m + 1 := by omega
          let i : Fin (m + 1) := ⟨k, hk_lt_adj⟩
          by_cases hzero : k = 0
          · subst k
            have hfirst_rate :
                binaryEndpointAwareAdjacentRate candidate sampleRate
                    (firstAdjacentIndex : Fin (m + 1)) =
                  binaryEndpointAwareAdjacentRate alt sampleRate
                    (firstAdjacentIndex : Fin (m + 1)) :=
              hrate_eq (firstAdjacentIndex : Fin (m + 1))
            have hfirst_eq :=
              binaryEndpointAwareAdjacentRate_first_high_eq_of_rate_eq
                hm sampleRate candidate alt hcandidate halt
                (hsample_high (firstAdjacentIndex : Fin (m + 1)))
                hfirst_rate
            simpa [firstAdjacentIndex, adjacentHighIndex] using hfirst_eq
          · have hlow_eq :
                candidate (adjacentLowIndex i) = alt (adjacentLowIndex i) := by
              have hk_le : k ≤ m + 1 := by omega
              simpa [i, adjacentLowIndex] using ih hk_le (by omega)
            have hfirst : i.val ≠ 0 := by
              simpa [i] using hzero
            have hlast : i.val ≠ m := by
              simpa [i] using hlast_coord
            have hrate_i : binaryEndpointAwareAdjacentRate candidate sampleRate i =
                binaryEndpointAwareAdjacentRate alt sampleRate i :=
              hrate_eq i
            have hhigh_eq :=
              binaryEndpointAwareAdjacentRate_interior_high_eq_of_low_eq_and_rate_eq
                sampleRate candidate alt hcandidate halt i hfirst hlast
                (hsample_high i) (hsample_low i) hlow_eq hrate_i
            simpa [i, adjacentHighIndex] using hhigh_eq
  funext θ
  have hθ : θ.val ≤ m + 1 := Nat.le_of_lt_succ θ.isLt
  simpa using hcoord θ.val hθ θ.isLt

/--
Uniform C.5 uniqueness bridge: the source's refined optimal chain is the
explicit doubled chain whenever both are endpoint-normalized and equalize the
uniform adjacent rates.  This connects Lemma 3.1 uniqueness to the C.5
doubling construction.
-/
theorem uniformDoubledEndpointLevels_eq_of_uniform_equalized_unique
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    {refinedLevels : Fin ((2 * m + 1) + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (hrefined : BinaryEndpointLevelVector refinedLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hrefinedEq :
      BinaryEndpointAwareAdjacentRatesEqualize refinedLevels
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))) :
    refinedLevels = uniformDoubledEndpointLevels oldLevels := by
  refine
    binaryEndpointAwareAdjacentRatesEqualize_unique
      (m := 2 * m + 1) (show 0 < 2 * m + 1 by omega)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
      refinedLevels (uniformDoubledEndpointLevels oldLevels)
      hrefined (uniformDoubledEndpointLevels_isEndpointLevelVector hm hold)
      ?_ ?_ hrefinedEq
      (uniformDoubledEndpointLevels_equalizes hm hold holdEq)
  · intro _i
    norm_num
  · intro _i
    norm_num

/--
One-step B.1 bracket consequence of C.5 plus uniqueness: every level in the
refined uniform equalized chain lies in a two-step bracket of the old chain.
This is the finite inclusion used by the source before iterating the dyadic
refinement.
-/
theorem uniformRefinedEndpointLevels_mem_two_step_interval_of_uniform_equalized_unique
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    {refinedLevels : Fin ((2 * m + 1) + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (hrefined : BinaryEndpointLevelVector refinedLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hrefinedEq :
      BinaryEndpointAwareAdjacentRatesEqualize refinedLevels
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)))
    (r : Fin ((2 * m + 1) + 2)) :
    ∃ i : Fin m,
      refinedLevels r ∈
        Set.Icc (oldLevels ⟨i.1, by omega⟩)
          (oldLevels ⟨i.1 + 2, by omega⟩) := by
  have hrefined_eq :
      refinedLevels = uniformDoubledEndpointLevels oldLevels :=
    uniformDoubledEndpointLevels_eq_of_uniform_equalized_unique
      hm hold hrefined holdEq hrefinedEq
  rw [hrefined_eq]
  exact uniformDoubledEndpointLevels_mem_two_step_interval hm hold r

/--
Sequence form of the C.5 uniqueness bridge: in any uniform equalized endpoint
level sequence, the level vector at the doubled index `2*m+1` is exactly the
explicit C.5 doubled vector built from the level vector at `m`.
-/
theorem uniformEqualizedLevelSequence_doubled_eq
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) :
    levels (2 * m + 1) = uniformDoubledEndpointLevels (levels m) :=
  uniformDoubledEndpointLevels_eq_of_uniform_equalized_unique
    hm (hlevels m) (hlevels (2 * m + 1)) (heq m) (heq (2 * m + 1))

/--
Sequence form of the one-step B.1 bracket inclusion: every level at the
doubled index `2*m+1` lies in a two-step bracket of the old level vector at
`m`, for any uniform equalized endpoint level sequence.
-/
theorem uniformEqualizedLevelSequence_doubled_mem_two_step_interval
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (r : Fin ((2 * m + 1) + 2)) :
    ∃ i : Fin m,
      levels (2 * m + 1) r ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) :=
  uniformRefinedEndpointLevels_mem_two_step_interval_of_uniform_equalized_unique
    hm (hlevels m) (hlevels (2 * m + 1)) (heq m) (heq (2 * m + 1)) r

/--
Indexed sequence form of the C.5 local inclusion.  In a uniform equalized level
sequence, if a level index at `2*m+1` lies between `2*i` and `2*i+2`, then the
corresponding level lies in the old two-step bracket `[t_i, t_{i+2}]`.
-/
theorem uniformEqualizedLevelSequence_doubled_mem_two_step_interval_of_index_between
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (i : Fin m) (r : Fin ((2 * m + 1) + 2))
    (hlo : 2 * i.1 ≤ r.1) (hhi : r.1 ≤ 2 * i.1 + 2) :
    levels (2 * m + 1) r ∈
      Set.Icc (levels m ⟨i.1, by omega⟩)
        (levels m ⟨i.1 + 2, by omega⟩) := by
  have hEq :
      levels (2 * m + 1) = uniformDoubledEndpointLevels (levels m) :=
    uniformEqualizedLevelSequence_doubled_eq levels hlevels heq hm
  rw [hEq]
  exact
    uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between
      hm (hlevels m) i r hlo hhi

/--
Four-point source-window sequence form of C.5.  This matches the reusable
floor-window theorem for `floor((2*M-1)*x)`.
-/
theorem uniformEqualizedLevelSequence_doubled_mem_two_step_interval_of_index_between_four
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (i : Fin m) (r : Fin ((2 * m + 1) + 2))
    (hlo : 2 * i.1 ≤ r.1) (hhi : r.1 ≤ 2 * i.1 + 3) :
    levels (2 * m + 1) r ∈
      Set.Icc (levels m ⟨i.1, by omega⟩)
        (levels m ⟨i.1 + 2, by omega⟩) := by
  have hEq :
      levels (2 * m + 1) = uniformDoubledEndpointLevels (levels m) :=
    uniformEqualizedLevelSequence_doubled_eq levels hlevels heq hm
  rw [hEq]
  exact
    uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between_four
      hm (hlevels m) i r hlo hhi

/--
Five-point source-window sequence form of C.5.  This extends the four-point
window by the copied even endpoint at the right boundary.
-/
theorem uniformEqualizedLevelSequence_doubled_mem_two_step_interval_of_index_between_five
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (i : Fin m) (r : Fin ((2 * m + 1) + 2))
    (hlo : 2 * i.1 ≤ r.1) (hhi : r.1 ≤ 2 * i.1 + 4) :
    levels (2 * m + 1) r ∈
      Set.Icc (levels m ⟨i.1, by omega⟩)
        (levels m ⟨i.1 + 2, by omega⟩) := by
  have hEq :
      levels (2 * m + 1) = uniformDoubledEndpointLevels (levels m) :=
    uniformEqualizedLevelSequence_doubled_eq levels hlevels heq hm
  rw [hEq]
  exact
    uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between_five
      hm (hlevels m) i r hlo hhi

/--
One-step source-window package for B.1: an old selected level whose index lies
between `i` and `i+2`, and a refined selected level whose index lies between
`2*i` and `2*i+2`, both lie in the same old two-step bracket.
-/
theorem uniformEqualizedLevelSequence_doubled_old_refined_mem_same_two_step_interval
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (i : Fin m) (oldIdx : Fin (m + 2))
    (refinedIdx : Fin ((2 * m + 1) + 2))
    (hold_lo : i.1 ≤ oldIdx.1) (hold_hi : oldIdx.1 ≤ i.1 + 2)
    (href_lo : 2 * i.1 ≤ refinedIdx.1)
    (href_hi : refinedIdx.1 ≤ 2 * i.1 + 2) :
    levels (2 * m + 1) refinedIdx ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) ∧
      levels m oldIdx ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) := by
  constructor
  · exact
      uniformEqualizedLevelSequence_doubled_mem_two_step_interval_of_index_between
        levels hlevels heq hm i refinedIdx href_lo href_hi
  · exact
      BinaryEndpointLevelVector_level_mem_two_step_interval_of_index_between
        (hlevels m) i oldIdx hold_lo hold_hi

/--
Four-point one-step source-window package for B.1.  This version accepts the
refined index window delivered by `nat_floor_two_mul_sub_one_mul_window`.
-/
theorem uniformEqualizedLevelSequence_doubled_old_refined_mem_same_two_step_interval_four
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (i : Fin m) (oldIdx : Fin (m + 2))
    (refinedIdx : Fin ((2 * m + 1) + 2))
    (hold_lo : i.1 ≤ oldIdx.1) (hold_hi : oldIdx.1 ≤ i.1 + 2)
    (href_lo : 2 * i.1 ≤ refinedIdx.1)
    (href_hi : refinedIdx.1 ≤ 2 * i.1 + 3) :
    levels (2 * m + 1) refinedIdx ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) ∧
      levels m oldIdx ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) := by
  constructor
  · exact
      uniformEqualizedLevelSequence_doubled_mem_two_step_interval_of_index_between_four
        levels hlevels heq hm i refinedIdx href_lo href_hi
  · exact
      BinaryEndpointLevelVector_level_mem_two_step_interval_of_index_between
        (hlevels m) i oldIdx hold_lo hold_hi

/--
Five-point one-step source-window package for B.1.  This is the boundary-safe
variant for clamped floor selectors.
-/
theorem uniformEqualizedLevelSequence_doubled_old_refined_mem_same_two_step_interval_five
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m)
    (i : Fin m) (oldIdx : Fin (m + 2))
    (refinedIdx : Fin ((2 * m + 1) + 2))
    (hold_lo : i.1 ≤ oldIdx.1) (hold_hi : oldIdx.1 ≤ i.1 + 2)
    (href_lo : 2 * i.1 ≤ refinedIdx.1)
    (href_hi : refinedIdx.1 ≤ 2 * i.1 + 4) :
    levels (2 * m + 1) refinedIdx ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) ∧
      levels m oldIdx ∈
        Set.Icc (levels m ⟨i.1, by omega⟩)
          (levels m ⟨i.1 + 2, by omega⟩) := by
  constructor
  · exact
      uniformEqualizedLevelSequence_doubled_mem_two_step_interval_of_index_between_five
        levels hlevels heq hm i refinedIdx href_lo href_hi
  · exact
      BinaryEndpointLevelVector_level_mem_two_step_interval_of_index_between
        (hlevels m) i oldIdx hold_lo hold_hi

/-- C.5 endpoint-vector index transform: a chain at `m` refines to `2*m+1`. -/
def uniformDoubledEndpointIndex (m : ℕ) : ℕ :=
  2 * m + 1

/--
Repeated C.5 endpoint-vector refinement.  The recursive definition keeps the
zero/successor equations definitional, which is important when these indices
appear inside dependent `Fin` types.
-/
def uniformDoubledEndpointIndexIterate (m : ℕ) : ℕ → ℕ
  | 0 => m
  | q + 1 => uniformDoubledEndpointIndex (uniformDoubledEndpointIndexIterate m q)

theorem uniformDoubledEndpointIndexIterate_zero (m : ℕ) :
    uniformDoubledEndpointIndexIterate m 0 = m := by
  rfl

theorem uniformDoubledEndpointIndexIterate_succ (m q : ℕ) :
    uniformDoubledEndpointIndexIterate m (q + 1) =
      uniformDoubledEndpointIndex (uniformDoubledEndpointIndexIterate m q) := by
  rfl

theorem uniformDoubledEndpointIndexIterate_pos_of_pos
    {m : ℕ} (hm : 0 < m) (q : ℕ) :
    0 < uniformDoubledEndpointIndexIterate m q := by
  induction q with
  | zero =>
      simpa [uniformDoubledEndpointIndexIterate] using hm
  | succ q ih =>
      change 0 <
        uniformDoubledEndpointIndex (uniformDoubledEndpointIndexIterate m q)
      unfold uniformDoubledEndpointIndex
      omega

/--
Closed form for repeated C.5 endpoint-vector refinement.  Adding one to the
index removes the affine offset: `m ↦ 2m+1` becomes multiplication by two.
-/
theorem uniformDoubledEndpointIndexIterate_add_one
    (m q : ℕ) :
    uniformDoubledEndpointIndexIterate m q + 1 = 2 ^ q * (m + 1) := by
  induction q with
  | zero =>
      simp [uniformDoubledEndpointIndexIterate]
  | succ q ih =>
      calc
        uniformDoubledEndpointIndexIterate m (q + 1) + 1 =
            2 * (uniformDoubledEndpointIndexIterate m q + 1) := by
          rw [uniformDoubledEndpointIndexIterate_succ,
            uniformDoubledEndpointIndex]
          omega
        _ = 2 * (2 ^ q * (m + 1)) := by rw [ih]
        _ = 2 ^ (q + 1) * (m + 1) := by
          rw [pow_succ]
          ring

/-- Repeated C.5 endpoint-index refinement composes additively. -/
theorem uniformDoubledEndpointIndexIterate_comp
    (m a b : ℕ) :
    uniformDoubledEndpointIndexIterate
        (uniformDoubledEndpointIndexIterate m a) b =
      uniformDoubledEndpointIndexIterate m (a + b) := by
  apply Nat.succ.inj
  change
    uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m a) b + 1 =
      uniformDoubledEndpointIndexIterate m (a + b) + 1
  rw [uniformDoubledEndpointIndexIterate_add_one,
    uniformDoubledEndpointIndexIterate_add_one,
    uniformDoubledEndpointIndexIterate_add_one]
  rw [pow_add]
  ring

/--
Closed form for a dyadic tail of repeated endpoint refinement.  Starting from
the level count at anchor `M`, the later count at `N` is obtained by scaling
`m+1` by `2^(N-M)`.
-/
theorem uniformDoubledEndpointIndexIterate_add_one_tail
    (m M N : ℕ) (hMN : M ≤ N) :
    uniformDoubledEndpointIndexIterate m N + 1 =
      2 ^ (N - M) * (uniformDoubledEndpointIndexIterate m M + 1) := by
  have hcomp :
      uniformDoubledEndpointIndexIterate
          (uniformDoubledEndpointIndexIterate m M) (N - M) =
        uniformDoubledEndpointIndexIterate m N := by
    rw [uniformDoubledEndpointIndexIterate_comp]
    rw [Nat.add_sub_of_le hMN]
  rw [← hcomp]
  exact
    uniformDoubledEndpointIndexIterate_add_one
      (uniformDoubledEndpointIndexIterate m M) (N - M)

/--
Denominator comparison for a dyadic tail of repeated endpoint refinement.  It
is the arithmetic step used to convert an old-grid cell-error bound into the
scaled refined-grid cell-error bound.
-/
theorem uniformDoubledEndpointIndexIterate_add_two_le_tail_scale_add_two
    (m M N : ℕ) (hMN : M ≤ N) :
    uniformDoubledEndpointIndexIterate m N + 2 ≤
      2 ^ (N - M) * (uniformDoubledEndpointIndexIterate m M + 2) := by
  let scale : ℕ := 2 ^ (N - M)
  let old : ℕ := uniformDoubledEndpointIndexIterate m M
  have htail :
      uniformDoubledEndpointIndexIterate m N + 1 = scale * (old + 1) := by
    simpa [scale, old] using
      uniformDoubledEndpointIndexIterate_add_one_tail m M N hMN
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  calc
    uniformDoubledEndpointIndexIterate m N + 2 =
        scale * (old + 1) + 1 := by omega
    _ ≤ scale * (old + 1) + scale := by
        exact Nat.add_le_add_left (Nat.succ_le_of_lt hscale_pos) _
    _ = scale * (old + 2) := by ring

/-- The quarter-rate decay factor equals the square of the dyadic scale. -/
theorem one_fourth_pow_eq_inv_two_pow_sq (q : ℕ) :
    ((1 / 4 : ℝ) ^ q) = 1 / (((2 ^ q : ℕ) : ℝ) ^ 2) := by
  have hcast : (((2 ^ q : ℕ) : ℝ) ^ 2) = (4 : ℝ) ^ q := by
    rw [Nat.cast_pow]
    rw [← pow_mul]
    rw [mul_comm q 2]
    rw [pow_mul]
    norm_num
  rw [hcast]
  rw [one_div_pow]

/--
Along an iterated C.5 refinement chain, the uniform equalized worst-adjacent
rate decays by at least the one-quarter factor at every refinement step.
-/
theorem uniformEqualizedLevelSequence_iterated_objective_rate_le_pow_one_fourth
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) (q : ℕ) :
    binaryEndpointAwareAdjacentRateObjective
        (levels (uniformDoubledEndpointIndexIterate m q))
        (fun _ : Fin ((uniformDoubledEndpointIndexIterate m q) + 2) => (1 : ℝ)) ≤
      (1 / 4 : ℝ) ^ q *
        binaryEndpointAwareAdjacentRateObjective
          (levels m) (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  induction q with
  | zero =>
      simp [uniformDoubledEndpointIndexIterate]
  | succ q ih =>
      let mOld : ℕ := uniformDoubledEndpointIndexIterate m q
      have hmOld : 0 < mOld :=
        uniformDoubledEndpointIndexIterate_pos_of_pos hm q
      have hstep :
          binaryEndpointAwareAdjacentRateObjective
              (levels (uniformDoubledEndpointIndex mOld))
              (fun _ : Fin ((uniformDoubledEndpointIndex mOld) + 2) => (1 : ℝ)) ≤
            (1 / 4 : ℝ) *
              binaryEndpointAwareAdjacentRateObjective
                (levels mOld) (fun _ : Fin (mOld + 2) => (1 : ℝ)) := by
        have hdouble :
            binaryEndpointAwareAdjacentRateObjective
                (uniformDoubledEndpointLevels (levels mOld))
                (fun _ : Fin ((2 * mOld + 1) + 2) => (1 : ℝ)) ≤
              (1 / 4 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective
                  (levels mOld) (fun _ : Fin (mOld + 2) => (1 : ℝ)) :=
          uniformDoubledEndpointLevels_objective_rate_le_one_fourth_old_objective
            hmOld (hlevels mOld) (heq mOld)
        have hEq :
            levels (2 * mOld + 1) =
              uniformDoubledEndpointLevels (levels mOld) :=
          uniformEqualizedLevelSequence_doubled_eq
            levels hlevels heq hmOld
        simpa [uniformDoubledEndpointIndex, hEq] using hdouble
      change
        binaryEndpointAwareAdjacentRateObjective
            (levels (uniformDoubledEndpointIndex mOld))
            (fun _ : Fin ((uniformDoubledEndpointIndex mOld) + 2) => (1 : ℝ)) ≤
          (1 / 4 : ℝ) ^ (q + 1) *
            binaryEndpointAwareAdjacentRateObjective
              (levels m) (fun _ : Fin (m + 2) => (1 : ℝ))
      calc
        binaryEndpointAwareAdjacentRateObjective
            (levels (uniformDoubledEndpointIndex mOld))
            (fun _ : Fin ((uniformDoubledEndpointIndex mOld) + 2) => (1 : ℝ))
            ≤
          (1 / 4 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective
              (levels mOld) (fun _ : Fin (mOld + 2) => (1 : ℝ)) := hstep
        _ ≤
          (1 / 4 : ℝ) *
            ((1 / 4 : ℝ) ^ q *
              binaryEndpointAwareAdjacentRateObjective
                (levels m) (fun _ : Fin (m + 2) => (1 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ =
          (1 / 4 : ℝ) ^ (q + 1) *
            binaryEndpointAwareAdjacentRateObjective
              (levels m) (fun _ : Fin (m + 2) => (1 : ℝ)) := by
            rw [pow_succ]
            ring

/--
The squared max adjacent mesh along an iterated C.5 refinement chain is
bounded by the geometrically decaying starting objective rate.
-/
theorem uniformEqualizedLevelSequence_iterated_maxWidth_sq_le_pow_one_fourth_objective
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) (q : ℕ) :
    (binaryEndpointAdjacentMaxWidth
        (m := uniformDoubledEndpointIndexIterate m q)
        (levels (uniformDoubledEndpointIndexIterate m q))) ^ 2 ≤
      (1 / 4 : ℝ) ^ q *
        binaryEndpointAwareAdjacentRateObjective
          (levels m) (fun _ : Fin (m + 2) => (1 : ℝ)) := by
  have hmIter : 0 < uniformDoubledEndpointIndexIterate m q :=
    uniformDoubledEndpointIndexIterate_pos_of_pos hm q
  exact
    (binaryEndpointAdjacentMaxWidth_sq_le_objective_of_uniform_equalized
      hmIter (hlevels (uniformDoubledEndpointIndexIterate m q))
      (heq (uniformDoubledEndpointIndexIterate m q))).trans
      (uniformEqualizedLevelSequence_iterated_objective_rate_le_pow_one_fourth
        levels hlevels heq hm q)

/--
Dyadic C.5 refinements have a linear adjacent-mesh bound along each fixed
starting anchor.  The constant depends only on the starting finite objective,
which is enough for B.1 because each dyadic subsequence fixes its anchor.
-/
theorem uniformEqualizedLevelSequence_iterated_maxWidth_le_start_objective_add_one_div
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) (q : ℕ) :
    binaryEndpointAdjacentMaxWidth
        (m := uniformDoubledEndpointIndexIterate m q)
        (levels (uniformDoubledEndpointIndexIterate m q)) ≤
      (((m + 1 : ℕ) : ℝ) *
          (binaryEndpointAwareAdjacentRateObjective
              (levels m) (fun _ : Fin (m + 2) => (1 : ℝ)) + 1)) /
        (((uniformDoubledEndpointIndexIterate m q + 1 : ℕ) : ℝ)) := by
  let maxW : ℝ :=
    binaryEndpointAdjacentMaxWidth
      (m := uniformDoubledEndpointIndexIterate m q)
      (levels (uniformDoubledEndpointIndexIterate m q))
  let A : ℝ :=
    binaryEndpointAwareAdjacentRateObjective
      (levels m) (fun _ : Fin (m + 2) => (1 : ℝ))
  let scale : ℝ := ((2 ^ q : ℕ) : ℝ)
  let startDen : ℝ := (((m + 1 : ℕ) : ℝ))
  have hmax_nonneg : 0 ≤ maxW := by
    dsimp [maxW]
    exact binaryEndpointAdjacentMaxWidth_nonneg
      (hlevels (uniformDoubledEndpointIndexIterate m q))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have hobj_eq :
        binaryEndpointAwareAdjacentRateObjective
            (levels m) (fun _ : Fin (m + 2) => (1 : ℝ)) =
          binaryEndpointAwareAdjacentRate
            (levels m) (fun _ : Fin (m + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (m + 1)) :=
      binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
        (levels m) (fun _ : Fin (m + 2) => (1 : ℝ)) (heq m)
        (firstAdjacentIndex : Fin (m + 1))
    rw [hobj_eq]
    exact le_of_lt
      (binaryEndpointAwareAdjacentRate_pos
        hm (levels m) (fun _ : Fin (m + 2) => (1 : ℝ))
        (hlevels m) (by intro _i; norm_num) (by intro _i; norm_num)
        (firstAdjacentIndex : Fin (m + 1)))
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hstartDen_pos : 0 < startDen := by
    dsimp [startDen]
    positivity
  have hden_eq :
      (((uniformDoubledEndpointIndexIterate m q + 1 : ℕ) : ℝ)) =
        scale * startDen := by
    dsimp [scale, startDen]
    rw [uniformDoubledEndpointIndexIterate_add_one]
    norm_num [Nat.cast_mul]
  have hsq :
      maxW ^ 2 ≤ (1 / scale ^ 2) * A := by
    have hraw :=
      uniformEqualizedLevelSequence_iterated_maxWidth_sq_le_pow_one_fourth_objective
        levels hlevels heq hm q
    have hraw' : maxW ^ 2 ≤ ((1 / 4 : ℝ) ^ q) * A := by
      simpa [maxW, A] using hraw
    have hscale_sq_eq : scale ^ 2 = (4 : ℝ) ^ q := by
      dsimp [scale]
      rw [Nat.cast_pow]
      rw [← pow_mul]
      rw [mul_comm q 2]
      rw [pow_mul]
      norm_num
    simpa [one_div, hscale_sq_eq] using hraw'
  have hsq_target :
      maxW ^ 2 ≤ ((A + 1) / scale) ^ 2 := by
    have hdiv_le : (1 / scale ^ 2) * A ≤ ((A + 1) / scale) ^ 2 := by
      have hscale_sq_pos : 0 < scale ^ 2 := sq_pos_of_pos hscale_pos
      rw [div_pow]
      field_simp [ne_of_gt hscale_sq_pos]
      nlinarith [sq_nonneg A]
    exact hsq.trans hdiv_le
  have htarget_nonneg : 0 ≤ (A + 1) / scale := by
    exact div_nonneg (by linarith) hscale_pos.le
  have hle_sqrt : maxW ≤ (A + 1) / scale :=
    (sq_le_sq₀ hmax_nonneg htarget_nonneg).mp hsq_target
  have htarget_eq :
      (A + 1) / scale =
        (startDen * (A + 1)) /
          (((uniformDoubledEndpointIndexIterate m q + 1 : ℕ) : ℝ)) := by
    rw [hden_eq]
    field_simp [ne_of_gt hscale_pos, ne_of_gt hstartDen_pos]
  simpa [maxW, A, startDen] using hle_sqrt.trans_eq htarget_eq

/-- Repeated C.5 endpoint-index refinement never decreases the endpoint index. -/
theorem uniformDoubledEndpointIndexIterate_self_le
    (m q : ℕ) :
    m ≤ uniformDoubledEndpointIndexIterate m q := by
  have hpow_pos : 0 < 2 ^ q :=
    Nat.pow_pos (by norm_num : 0 < (2 : ℕ))
  have hmul :
      m + 1 ≤ 2 ^ q * (m + 1) :=
    Nat.le_mul_of_pos_left (m + 1) hpow_pos
  have hadd := uniformDoubledEndpointIndexIterate_add_one m q
  omega

/-- Appendix B source recurrence for interval counts: `M ↦ 2M - 1`. -/
def theoremB1SourceDoubledIndex (M : ℕ) : ℕ :=
  2 * (M - 1) + 1

/-- Repeated Appendix B source recurrence. -/
def theoremB1SourceDoubledIndexIterate (M : ℕ) : ℕ → ℕ
  | 0 => M
  | q + 1 => theoremB1SourceDoubledIndex
      (theoremB1SourceDoubledIndexIterate M q)

theorem theoremB1SourceDoubledIndexIterate_zero (M : ℕ) :
    theoremB1SourceDoubledIndexIterate M 0 = M := by
  rfl

theorem theoremB1SourceDoubledIndexIterate_succ (M q : ℕ) :
    theoremB1SourceDoubledIndexIterate M (q + 1) =
      theoremB1SourceDoubledIndex
        (theoremB1SourceDoubledIndexIterate M q) := by
  rfl

/--
Closed form used in the source proof of Theorem B.1:
`M_q = 2^q (M - 1) + 1`.
-/
theorem theoremB1SourceDoubledIndexIterate_eq
    {M : ℕ} (hM : 0 < M) (q : ℕ) :
    theoremB1SourceDoubledIndexIterate M q =
      2 ^ q * (M - 1) + 1 := by
  induction q with
  | zero =>
      simp [theoremB1SourceDoubledIndexIterate]
      omega
  | succ q ih =>
      rw [theoremB1SourceDoubledIndexIterate_succ,
        theoremB1SourceDoubledIndex, ih]
      simp
      rw [pow_succ]
      ring

/--
This definition is propositionally equal to the source display `2M - 1` for
positive interval counts.
-/
theorem theoremB1SourceDoubledIndex_eq_two_mul_sub_one
    {M : ℕ} (hM : 0 < M) :
    theoremB1SourceDoubledIndex M = 2 * M - 1 := by
  unfold theoremB1SourceDoubledIndex
  omega

/--
The previous closed form is the same as the source text's
`M_q = 2^q M - 2^q + 1`.
-/
theorem theoremB1SourceDoubledIndexIterate_eq_source_formula
    {M : ℕ} (hM : 0 < M) (q : ℕ) :
    theoremB1SourceDoubledIndexIterate M q =
      2 ^ q * M - 2 ^ q + 1 := by
  rw [theoremB1SourceDoubledIndexIterate_eq hM q]
  rw [Nat.mul_sub_left_distrib]
  have hle : 2 ^ q ≤ 2 ^ q * M := by
    exact Nat.le_mul_of_pos_right (2 ^ q) hM
  omega

/--
Source-shaped q-step floor window for Appendix B.  This is the reusable
arithmetic input behind the statement that the selected level at
`M_q = 2^q M - 2^q + 1` remains in the dyadic block around the selected level
at `M`.
-/
theorem theoremB1SourceDoubledIndexIterate_floor_window
    {M q : ℕ} (hM : 0 < M) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let old := Nat.floor ((M : ℝ) * θ)
    let refined :=
      Nat.floor (((theoremB1SourceDoubledIndexIterate M q : ℕ) : ℝ) * θ)
    refined ≤ 2 ^ q * old + 2 ^ q ∧
      2 ^ q * old ≤ refined + 2 ^ q := by
  have h :=
    AppliedModelingLib.Math.nat_floor_dyadic_pred_add_one_mul_window
      (M := M) (q := q) hM hθ0 hθ1
  simpa [theoremB1SourceDoubledIndexIterate_eq hM q] using h

/--
Arithmetic selector for one induction step in the Appendix B block argument.
If a refined index lies in the doubled large window
`[2*scale*i, 2*scale*(i+2)]`, then some previous-stage index `j` lies in the
scaled old window and has five-point C.5 window containing the refined index.
-/
theorem exists_index_for_scaled_two_step_window
    {scale n i r : ℕ} (hscale : 0 < scale)
    (hupper : scale * (i + 2) ≤ n + 1)
    (hlo : 2 * scale * i ≤ r)
    (hhi : r ≤ 2 * scale * (i + 2)) :
    ∃ j : Fin n,
      scale * i ≤ j.1 ∧
      j.1 + 2 ≤ scale * (i + 2) ∧
      2 * j.1 ≤ r ∧
      r ≤ 2 * j.1 + 4 := by
  let upper : ℕ := scale * (i + 2) - 2
  let jVal : ℕ := min (r / 2) upper
  have hupper_plus : upper + 2 = scale * (i + 2) := by
    dsimp [upper]
    have htwo_le : 2 ≤ scale * (i + 2) := by
      have hscale_two : 1 * 2 ≤ scale * (i + 2) :=
        Nat.mul_le_mul hscale (by omega)
      simpa using hscale_two
    omega
  have hupper_lt_n : upper < n := by
    have hle : upper + 2 ≤ n + 1 := by
      simpa [hupper_plus] using hupper
    omega
  have hleft_upper : scale * i ≤ upper := by
    have hmul : scale * (i + 2) = scale * i + 2 * scale := by ring
    have hupper_eq : upper = scale * (i + 2) - 2 := rfl
    rw [hupper_eq, hmul]
    omega
  have hleft_div : scale * i ≤ r / 2 := by
    exact (Nat.le_div_iff_mul_le Nat.zero_lt_two).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hlo)
  by_cases hdiv_le : r / 2 ≤ upper
  · refine ⟨⟨jVal, by dsimp [jVal]; omega⟩, ?_, ?_, ?_, ?_⟩
    · dsimp [jVal]
      rw [min_eq_left hdiv_le]
      exact hleft_div
    · dsimp [jVal]
      rw [min_eq_left hdiv_le]
      omega
    · dsimp [jVal]
      rw [min_eq_left hdiv_le]
      have hmod := Nat.div_add_mod r 2
      have hmod_lt : r % 2 < 2 := Nat.mod_lt r (by norm_num)
      omega
    · dsimp [jVal]
      rw [min_eq_left hdiv_le]
      have hmod := Nat.div_add_mod r 2
      have hmod_lt : r % 2 < 2 := Nat.mod_lt r (by norm_num)
      omega
  · have hupper_lt_div : upper < r / 2 := by omega
    refine ⟨⟨jVal, by dsimp [jVal]; omega⟩, ?_, ?_, ?_, ?_⟩
    · dsimp [jVal]
      rw [min_eq_right (by omega : upper ≤ r / 2)]
      exact hleft_upper
    · dsimp [jVal]
      rw [min_eq_right (by omega : upper ≤ r / 2)]
      exact le_of_eq hupper_plus
    · dsimp [jVal]
      rw [min_eq_right (by omega : upper ≤ r / 2)]
      have hlt_mul :
          2 * upper ≤ r := by
        have hsucc_le : upper + 1 ≤ r / 2 := Nat.succ_le_of_lt hupper_lt_div
        have hmul_le : 2 * (upper + 1) ≤ r := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (Nat.le_div_iff_mul_le Nat.zero_lt_two).1 hsucc_le
        omega
      omega
    · dsimp [jVal]
      rw [min_eq_right (by omega : upper ≤ r / 2)]
      have htarget : 2 * scale * (i + 2) = 2 * upper + 4 := by
        calc
          2 * scale * (i + 2) = 2 * (scale * (i + 2)) := by ring
          _ = 2 * (upper + 2) := by rw [← hupper_plus]
          _ = 2 * upper + 4 := by ring
      exact hhi.trans_eq htarget

/--
Explicit q-times C.5 refinement of an endpoint level vector.  This lets later
Appendix B arguments state block-inclusion invariants directly over the
iterated refined chain.
-/
def uniformDoubledEndpointLevelsIterate {m : ℕ}
    (oldLevels : Fin (m + 2) → ℝ) :
    (q : ℕ) →
      Fin ((uniformDoubledEndpointIndexIterate m q) + 2) → ℝ
  | 0 => oldLevels
  | q + 1 =>
      uniformDoubledEndpointLevels
        (uniformDoubledEndpointLevelsIterate oldLevels q)

theorem uniformDoubledEndpointLevelsIterate_zero
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) :
    uniformDoubledEndpointLevelsIterate oldLevels 0 = oldLevels := by
  rfl

theorem uniformDoubledEndpointLevelsIterate_succ
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) (q : ℕ) :
    uniformDoubledEndpointLevelsIterate oldLevels (q + 1) =
      uniformDoubledEndpointLevels
        (uniformDoubledEndpointLevelsIterate oldLevels q) := by
  rfl

/--
Any uniform equalized endpoint-level sequence is obtained by explicitly
iterating the C.5 doubled construction from its starting level vector.
-/
theorem uniformEqualizedLevelSequence_iterated_eq
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m : ℕ} (hm : 0 < m) (q : ℕ) :
    levels (uniformDoubledEndpointIndexIterate m q) =
      uniformDoubledEndpointLevelsIterate (levels m) q := by
  induction q with
  | zero =>
      rfl
  | succ q ih =>
      change
        levels
            (uniformDoubledEndpointIndex
              (uniformDoubledEndpointIndexIterate m q)) =
          uniformDoubledEndpointLevels
            (uniformDoubledEndpointLevelsIterate (levels m) q)
      have hstep :
          levels
              (uniformDoubledEndpointIndex
                (uniformDoubledEndpointIndexIterate m q)) =
            uniformDoubledEndpointLevels
              (levels (uniformDoubledEndpointIndexIterate m q)) := by
        simpa [uniformDoubledEndpointIndex] using
          uniformEqualizedLevelSequence_doubled_eq
            levels hlevels heq
            (uniformDoubledEndpointIndexIterate_pos_of_pos hm q)
      rw [hstep, ih]

/--
Endpoint-vector invariants are preserved by explicit repeated C.5 refinement.
-/
theorem uniformDoubledEndpointLevelsIterate_isEndpointLevelVector
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) (q : ℕ) :
    BinaryEndpointLevelVector
      (uniformDoubledEndpointLevelsIterate oldLevels q) := by
  induction q with
  | zero =>
      exact hold
  | succ q ih =>
      change BinaryEndpointLevelVector
        (uniformDoubledEndpointLevels
          (uniformDoubledEndpointLevelsIterate oldLevels q))
      exact
        uniformDoubledEndpointLevels_isEndpointLevelVector
          (uniformDoubledEndpointIndexIterate_pos_of_pos hm q) ih

/--
Block form of the repeated C.5 inclusion.  If a level index in the q-times
refined chain lies in the scaled two-step index window around `i`, then its
level lies in the original old bracket `[t_i, t_{i+2}]`.
-/
theorem uniformDoubledEndpointLevelsIterate_mem_two_step_interval_of_scaled_index_between
    {m q : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (i : Fin m)
    (r : Fin ((uniformDoubledEndpointIndexIterate m q) + 2))
    (hlo : 2 ^ q * i.1 ≤ r.1)
    (hhi : r.1 ≤ 2 ^ q * (i.1 + 2)) :
    uniformDoubledEndpointLevelsIterate oldLevels q r ∈
      Set.Icc (oldLevels ⟨i.1, by omega⟩)
        (oldLevels ⟨i.1 + 2, by omega⟩) := by
  induction q with
  | zero =>
      exact
        BinaryEndpointLevelVector_level_mem_two_step_interval_of_index_between
          hold i r (by simpa using hlo) (by simpa using hhi)
  | succ q ih =>
      let scale : ℕ := 2 ^ q
      change
        uniformDoubledEndpointLevels
            (uniformDoubledEndpointLevelsIterate oldLevels q) r ∈
          Set.Icc (oldLevels ⟨i.1, by omega⟩)
            (oldLevels ⟨i.1 + 2, by omega⟩)
      have hupper :
          scale * (i.1 + 2) ≤
            uniformDoubledEndpointIndexIterate m q + 1 := by
        dsimp [scale]
        rw [uniformDoubledEndpointIndexIterate_add_one]
        exact Nat.mul_le_mul_left (2 ^ q) (by omega)
      have hlo' : 2 * scale * i.1 ≤ r.1 := by
        dsimp [scale]
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hlo
      have hhi' : r.1 ≤ 2 * scale * (i.1 + 2) := by
        dsimp [scale]
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hhi
      rcases exists_index_for_scaled_two_step_window
          (scale := scale)
          (n := uniformDoubledEndpointIndexIterate m q)
          (i := i.1) (r := r.1)
          (by dsimp [scale]; positivity) hupper hlo' hhi' with
        ⟨j, hjlo, hjhi, hrlo, hrhi⟩
      have hstep :=
        uniformDoubledEndpointLevels_mem_two_step_interval_of_index_between_five
          (uniformDoubledEndpointIndexIterate_pos_of_pos hm q)
          (uniformDoubledEndpointLevelsIterate_isEndpointLevelVector hm hold q)
          j r hrlo hrhi
      let rlo : Fin ((uniformDoubledEndpointIndexIterate m q) + 2) :=
        ⟨j.1, by omega⟩
      let rhi : Fin ((uniformDoubledEndpointIndexIterate m q) + 2) :=
        ⟨j.1 + 2, by omega⟩
      have hmem_lo :
          uniformDoubledEndpointLevelsIterate oldLevels q rlo ∈
            Set.Icc (oldLevels ⟨i.1, by omega⟩)
              (oldLevels ⟨i.1 + 2, by omega⟩) := by
        have hrlo_lo : 2 ^ q * i.1 ≤ rlo.1 := by
          simpa [rlo, scale] using hjlo
        have hrlo_hi : rlo.1 ≤ 2 ^ q * (i.1 + 2) := by
          dsimp [rlo, scale] at *
          omega
        exact ih rlo hrlo_lo hrlo_hi
      have hmem_hi :
          uniformDoubledEndpointLevelsIterate oldLevels q rhi ∈
            Set.Icc (oldLevels ⟨i.1, by omega⟩)
              (oldLevels ⟨i.1 + 2, by omega⟩) := by
        have hrhi_lo : 2 ^ q * i.1 ≤ rhi.1 := by
          dsimp [rhi, scale] at *
          omega
        have hrhi_hi : rhi.1 ≤ 2 ^ q * (i.1 + 2) := by
          simpa [rhi, scale] using hjhi
        exact ih rhi hrhi_lo hrhi_hi
      constructor
      · exact hmem_lo.1.trans hstep.1
      · exact hstep.2.trans hmem_hi.2

/--
Iterated-step form of the C.5 bracket inclusion.  At every repeated C.5 stage,
each level in the next refined chain lies in a two-step bracket of the previous
chain.
-/
theorem uniformEqualizedLevelSequence_iterated_step_mem_two_step_interval
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m)
    (r :
      Fin ((uniformDoubledEndpointIndex
        (uniformDoubledEndpointIndexIterate m q)) + 2)) :
    ∃ i : Fin (uniformDoubledEndpointIndexIterate m q),
      levels (uniformDoubledEndpointIndex
          (uniformDoubledEndpointIndexIterate m q)) r ∈
        Set.Icc
          (levels (uniformDoubledEndpointIndexIterate m q)
            ⟨i.1, by omega⟩)
          (levels (uniformDoubledEndpointIndexIterate m q)
            ⟨i.1 + 2, by omega⟩) := by
  simpa [uniformDoubledEndpointIndex] using
    uniformEqualizedLevelSequence_doubled_mem_two_step_interval
      levels hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm q) r

/--
Indexed iterated-step form of the C.5 bracket inclusion.  This is the direct
call shape for a source floor-window proof at an arbitrary repeated C.5 stage.
-/
theorem uniformEqualizedLevelSequence_iterated_step_mem_two_step_interval_of_index_between
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m)
    (i : Fin (uniformDoubledEndpointIndexIterate m q))
    (r :
      Fin ((uniformDoubledEndpointIndex
        (uniformDoubledEndpointIndexIterate m q)) + 2))
    (hlo : 2 * i.1 ≤ r.1) (hhi : r.1 ≤ 2 * i.1 + 2) :
    levels (uniformDoubledEndpointIndex
        (uniformDoubledEndpointIndexIterate m q)) r ∈
      Set.Icc
        (levels (uniformDoubledEndpointIndexIterate m q)
          ⟨i.1, by omega⟩)
        (levels (uniformDoubledEndpointIndexIterate m q)
          ⟨i.1 + 2, by omega⟩) := by
  simpa [uniformDoubledEndpointIndex] using
    uniformEqualizedLevelSequence_doubled_mem_two_step_interval_of_index_between
      levels hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm q) i r hlo hhi

/--
Iterated-step source-window package for B.1.  At any repeated C.5 stage, an
old selected index in `[i, i+2]` and a next-stage selected index in
`[2*i, 2*i+2]` give the same old two-step level bracket.
-/
theorem uniformEqualizedLevelSequence_iterated_step_old_refined_mem_same_two_step_interval
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {m q : ℕ} (hm : 0 < m)
    (i : Fin (uniformDoubledEndpointIndexIterate m q))
    (oldIdx : Fin (uniformDoubledEndpointIndexIterate m q + 2))
    (refinedIdx :
      Fin ((uniformDoubledEndpointIndex
        (uniformDoubledEndpointIndexIterate m q)) + 2))
    (hold_lo : i.1 ≤ oldIdx.1) (hold_hi : oldIdx.1 ≤ i.1 + 2)
    (href_lo : 2 * i.1 ≤ refinedIdx.1)
    (href_hi : refinedIdx.1 ≤ 2 * i.1 + 2) :
    levels (uniformDoubledEndpointIndex
        (uniformDoubledEndpointIndexIterate m q)) refinedIdx ∈
        Set.Icc
          (levels (uniformDoubledEndpointIndexIterate m q)
            ⟨i.1, by omega⟩)
          (levels (uniformDoubledEndpointIndexIterate m q)
            ⟨i.1 + 2, by omega⟩) ∧
      levels (uniformDoubledEndpointIndexIterate m q) oldIdx ∈
        Set.Icc
          (levels (uniformDoubledEndpointIndexIterate m q)
            ⟨i.1, by omega⟩)
          (levels (uniformDoubledEndpointIndexIterate m q)
            ⟨i.1 + 2, by omega⟩) := by
  simpa [uniformDoubledEndpointIndex] using
    uniformEqualizedLevelSequence_doubled_old_refined_mem_same_two_step_interval
      levels hlevels heq
      (uniformDoubledEndpointIndexIterate_pos_of_pos hm q)
      i oldIdx refinedIdx hold_lo hold_hi href_lo href_hi

/--
Finite Lemma 3.1 packaged uniqueness: once an equalized endpoint-aware level
vector exists, it is unique.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_exists
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hexists :
      ∃ candidate : Fin (m + 2) → ℝ,
        BinaryEndpointLevelVector candidate ∧
          BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    ∃! candidate : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector candidate ∧
        BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate := by
  rcases hexists with ⟨candidate, hcandidate, heq_candidate⟩
  refine ⟨candidate, ⟨hcandidate, heq_candidate⟩, ?_⟩
  intro alt halt_eq
  exact
    (binaryEndpointAwareAdjacentRatesEqualize_unique
      hm sampleRate candidate alt hcandidate halt_eq.1
      hsample_high hsample_low heq_candidate halt_eq.2).symm

/--
Conditional finite Lemma 3.1 unique existence from a scalar forward-cascade
certificate.  The existing uniqueness theorem handles uniqueness once the
certificate supplies an equalized feasible vector.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped_certificate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hlevels :
      BinaryEndpointLevelVector (binaryEndpointForwardClippedLevels sampleRate r))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  refine
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_exists
      (m := m) (show 0 < m by omega) sampleRate hsample_high hsample_low ?_
  exact
    binaryEndpointAwareAdjacentRatesEqualize_exists_of_forward_clipped_certificate
      hm sampleRate r hsample_high hsample_low hlevels hfeasible hgap

/--
Conditional finite Lemma 3.1 unique existence from a scalar forward-cascade
certificate, with endpoint-vector feasibility derived from terminal order.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped_scalar_certificate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hterminal :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
        binaryEndpointForwardClippedCap sampleRate r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  refine
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_exists
      (m := m) (show 0 < m by omega) sampleRate hsample_high hsample_low ?_
  exact
    binaryEndpointAwareAdjacentRatesEqualize_exists_of_forward_clipped_scalar_certificate
      hm sampleRate hr hsample_high hsample_low hfeasible hterminal hgap

/--
Finite Lemma 3.1 existence and uniqueness for chains with more than one
interior level, derived from the forward-clipped shooting construction.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  have hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) := by
    intro i
    have hraw := hsample_pos (i.val + 1) (by omega)
    rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
    simpa [adjacentHighIndex] using hraw
  have hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) := by
    intro i
    have hraw := hsample_pos i.val (by omega)
    rw [binaryEndpointSampleRateNat_of_lt sampleRate (by omega)] at hraw
    simpa [adjacentLowIndex] using hraw
  rcases
    binaryEndpointInverseGap_existsUnique_pos_zero_and_nonneg_iff
      (hsample_pos 1 (by omega)) (hsample_pos m (by omega)) with
    ⟨crossing, hcrossing, _hcrossing_unique⟩
  rcases hcrossing with ⟨hcrossing_pos, hcross, _hcrossing_nonneg⟩
  rcases
    binaryEndpointForwardClippedTerminalGap_exists_zero
      hm sampleRate hsample_pos hcrossing_pos hcross with
    ⟨r, hr_pos, hr_lt_crossing, hgap⟩
  have hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r := by
    intro n hn
    exact
      binaryEndpointForwardClippedLevelNat_step_feasible_of_terminal_gap_zero
        hm sampleRate hsample_pos hr_pos hgap n hn
  have hterminal :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
        binaryEndpointForwardClippedCap sampleRate r :=
    binaryEndpointForwardClippedPenultimate_lt_cap_of_terminal_gap_zero_of_le_inverseGap_crossing
      hm sampleRate hsample_pos hcross hr_pos (le_of_lt hr_lt_crossing) hgap
  exact
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped_scalar_certificate
      hm sampleRate hr_pos hsample_high hsample_low hfeasible hterminal hgap

/-- With one interior level, the equalized endpoint-aware vector exists uniquely. -/
theorem binaryEndpointAwareAdjacentRatesEqualize_existsUnique_one
    (sampleRate : Fin (1 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (1 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (1 + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∃! levels : Fin (1 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  refine
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_exists
      (m := 1) (by norm_num) sampleRate hsample_high hsample_low ?_
  exact
    ⟨binaryEndpointOneInteriorHalfLevel,
      binaryEndpointOneInteriorHalfLevel_isEndpointLevelVector,
      binaryEndpointOneInteriorHalfLevel_equalizes sampleRate⟩

/--
Two-interior-level target-rate packaging for Lemma 3.1.  If a positive target
rate makes the first endpoint inverse, middle closed rate, and last endpoint
inverse agree, then it produces an equalized endpoint-aware vector.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_exists_two_of_target_rate
    (sampleRate : Fin (2 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentLowIndex i))
    {r : ℝ} (hr : 0 < r)
    (horder :
      binaryEndpointFirstLevelOfRate
          (sampleRate
            (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r <
        binaryEndpointLastLevelOfRate
          (sampleRate
            (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
    (hmiddle :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex (1 : Fin (2 + 1))))
          (sampleRate (adjacentLowIndex (1 : Fin (2 + 1))))
          (binaryEndpointLastLevelOfRate
            (sampleRate
              (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
          (binaryEndpointFirstLevelOfRate
            (sampleRate
              (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r) =
        r) :
    ∃ levels : Fin (2 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  let pFirst : ℝ :=
    binaryEndpointFirstLevelOfRate
      (sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r
  let pLast : ℝ :=
    binaryEndpointLastLevelOfRate
      (sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r
  let levels : Fin (2 + 2) → ℝ := fun i =>
    if i.val = 0 then 0
    else if i.val = 1 then pFirst
    else if i.val = 2 then pLast
    else 1
  have hpFirst_mem : pFirst ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [pFirst]
    exact binaryEndpointFirstLevelOfRate_mem_Ioo
      (hsample_high (firstAdjacentIndex : Fin (2 + 1))) hr
  have hpLast_mem : pLast ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [pLast]
    exact binaryEndpointLastLevelOfRate_mem_Ioo
      (hsample_low (lastAdjacentIndex : Fin (2 + 1))) hr
  have horder' : pFirst < pLast := by
    simpa [pFirst, pLast] using horder
  have hlevels : BinaryEndpointLevelVector levels := by
    constructor
    · simp [levels, firstLevelIndex]
    constructor
    · simp [levels, lastLevelIndex]
    · intro i
      fin_cases i
      · simpa [levels, adjacentLowIndex, adjacentHighIndex] using
          hpFirst_mem.1
      · simpa [levels, adjacentLowIndex, adjacentHighIndex] using horder'
      · simpa [levels, adjacentLowIndex, adjacentHighIndex] using
          hpLast_mem.2
  have hall :
      ∀ i : Fin (2 + 1),
        binaryEndpointAwareAdjacentRate levels sampleRate i = r := by
    intro i
    fin_cases i
    · have hfirst :=
        binaryEndpointFirstLevelOfRate_realizes
          (hsample_high (firstAdjacentIndex : Fin (2 + 1)))
          (r := r)
      simpa [levels, pFirst, binaryEndpointAwareAdjacentRate,
        firstAdjacentIndex, adjacentLowIndex, adjacentHighIndex] using hfirst
    · simpa [levels, pFirst, pLast, binaryEndpointAwareAdjacentRate,
        adjacentLowIndex, adjacentHighIndex] using hmiddle
    · have hlast :=
        binaryEndpointLastLevelOfRate_realizes
          (hsample_low (lastAdjacentIndex : Fin (2 + 1)))
          (r := r)
      simpa [levels, pLast, binaryEndpointAwareAdjacentRate,
        lastAdjacentIndex, adjacentLowIndex, adjacentHighIndex] using hlast
  refine ⟨levels, hlevels, ?_⟩
  intro i j
  rw [hall i, hall j]

/--
Two-interior-level target-rate packaging for Lemma 3.1, in unique-existence
form.  The general uniqueness theorem discharges uniqueness once the scalar
target-rate equation supplies existence.
-/
theorem binaryEndpointAwareAdjacentRatesEqualize_existsUnique_two_of_target_rate
    (sampleRate : Fin (2 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentLowIndex i))
    {r : ℝ} (hr : 0 < r)
    (horder :
      binaryEndpointFirstLevelOfRate
          (sampleRate
            (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r <
        binaryEndpointLastLevelOfRate
          (sampleRate
            (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
    (hmiddle :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex (1 : Fin (2 + 1))))
          (sampleRate (adjacentLowIndex (1 : Fin (2 + 1))))
          (binaryEndpointLastLevelOfRate
            (sampleRate
              (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
          (binaryEndpointFirstLevelOfRate
            (sampleRate
              (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r) =
        r) :
    ∃! levels : Fin (2 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  refine
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_exists
      (m := 2) (by norm_num) sampleRate hsample_high hsample_low ?_
  exact
    binaryEndpointAwareAdjacentRatesEqualize_exists_two_of_target_rate
      sampleRate hsample_high hsample_low hr horder hmiddle

/-- With two interior levels, the equalized endpoint-aware vector exists uniquely. -/
theorem binaryEndpointAwareAdjacentRatesEqualize_existsUnique_two
    (sampleRate : Fin (2 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∃! levels : Fin (2 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate := by
  let gLo : ℝ :=
    sampleRate (adjacentLowIndex (1 : Fin (2 + 1)))
  let gHi : ℝ :=
    sampleRate (adjacentHighIndex (1 : Fin (2 + 1)))
  have hgLo : 0 < gLo := by
    dsimp [gLo]
    exact hsample_low (1 : Fin (2 + 1))
  have hgHi : 0 < gHi := by
    dsimp [gHi]
    exact hsample_high (1 : Fin (2 + 1))
  rcases
    binaryEndpointTwoInteriorMiddleRateGap_exists_zero
      (gLo := gLo) (gHi := gHi) hgLo hgHi with
    ⟨r, hr, horder, hgap⟩
  refine
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_two_of_target_rate
      sampleRate hsample_high hsample_low hr ?_ ?_
  · simpa [gLo, gHi, firstAdjacentIndex, lastAdjacentIndex,
      adjacentLowIndex, adjacentHighIndex] using horder
  · have hmiddle :
        binaryEndpointTwoInteriorMiddleRate gLo gHi r = r := by
      dsimp [binaryEndpointTwoInteriorMiddleRateGap] at hgap
      linarith
    simpa [binaryEndpointTwoInteriorMiddleRate, gLo, gHi,
      firstAdjacentIndex, lastAdjacentIndex, adjacentLowIndex,
      adjacentHighIndex] using hmiddle

/--
Finite Lemma 3.1 strict maximin theorem: an endpoint-normalized level vector
that equalizes all adjacent endpoint-aware rates is the unique maximizer of
the finite worst-adjacent rate objective.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isStrictMaximizerOn_of_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r) :
    AppliedModelingLib.Optimization.IsStrictMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  constructor
  · exact hcandidate
  · intro alt halt hne
    have hcandidate_obj :
        binaryEndpointAwareAdjacentRateObjective candidate sampleRate = r :=
      binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
        candidate sampleRate r heq
    by_contra hnot_lt
    have hobj_ge :
        r ≤ binaryEndpointAwareAdjacentRateObjective alt sampleRate := by
      have hge :
          binaryEndpointAwareAdjacentRateObjective candidate sampleRate ≤
            binaryEndpointAwareAdjacentRateObjective alt sampleRate :=
        le_of_not_gt hnot_lt
      simpa [hcandidate_obj] using hge
    have hrate_ge :
        ∀ i : Fin (m + 1),
          r ≤ binaryEndpointAwareAdjacentRate alt sampleRate i := by
      intro i
      exact hobj_ge.trans
        (by
          unfold binaryEndpointAwareAdjacentRateObjective
          exact AppliedModelingLib.finiteMin_le
            (binaryEndpointAwareAdjacentRate alt sampleRate) i)
    let c : ℕ → ℝ := fun n =>
      if h : n < m + 2 then candidate ⟨n, h⟩ else 0
    let a : ℕ → ℝ := fun n =>
      if h : n < m + 2 then alt ⟨n, h⟩ else 0
    have hge_coord :
        ∀ n : ℕ, n ≤ m → c n ≤ a n := by
      intro n hn
      induction n with
      | zero =>
          have h0 : 0 < m + 2 := by omega
          have hc0 : c 0 = 0 := by
            simpa [c, h0, firstLevelIndex] using hcandidate.1
          have ha0 : a 0 = 0 := by
            simpa [a, h0, firstLevelIndex] using halt.1
          rw [hc0, ha0]
      | succ n ih =>
          by_cases hlast_coord : n = m
          · omega
          · have hn_lt_m : n < m := by omega
            have hn_lt_adj : n < m + 1 := by omega
            let i : Fin (m + 1) := ⟨n, hn_lt_adj⟩
            by_cases hzero : n = 0
            · subst n
              by_contra hnot
              have hhigh_lt : a 1 < c 1 := lt_of_not_ge hnot
              have hrate_lt :
                  binaryEndpointAwareAdjacentRate alt sampleRate
                      (firstAdjacentIndex : Fin (m + 1)) <
                    binaryEndpointAwareAdjacentRate candidate sampleRate
                      (firstAdjacentIndex : Fin (m + 1)) := by
                have hhigh_fin :
                    alt (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) <
                      candidate (adjacentHighIndex
                        (firstAdjacentIndex : Fin (m + 1))) := by
                  have h1 : 1 < m + 2 := by omega
                  simpa [a, c, h1, firstAdjacentIndex, adjacentHighIndex]
                    using hhigh_lt
                exact
                  binaryEndpointAwareAdjacentRate_first_lt_of_high_lt
                    hm sampleRate alt candidate halt hcandidate
                    (hsample_high (firstAdjacentIndex : Fin (m + 1)))
                    hhigh_fin
              have hrate_candidate :
                  binaryEndpointAwareAdjacentRate candidate sampleRate
                      (firstAdjacentIndex : Fin (m + 1)) = r :=
                heq (firstAdjacentIndex : Fin (m + 1))
              exact
                (not_lt_of_ge
                  ((hrate_candidate.symm ▸
                    hrate_ge (firstAdjacentIndex : Fin (m + 1)))))
                  hrate_lt
            · have hfirst : i.val ≠ 0 := by
                simpa [i] using hzero
              have hlast : i.val ≠ m := by
                simpa [i] using hlast_coord
              have hlow_le_fin :
                  candidate (adjacentLowIndex i) ≤ alt (adjacentLowIndex i) := by
                have hle_nat : c n ≤ a n := ih hn_lt_m.le
                have hn_bound : n < m + 2 := by omega
                simpa [c, a, i, adjacentLowIndex, hn_bound] using hle_nat
              by_contra hnot
              have hhi_lt_nat : a (n + 1) < c (n + 1) := lt_of_not_ge hnot
              have hhi_lt_fin :
                  alt (adjacentHighIndex i) < candidate (adjacentHighIndex i) := by
                have hn1_bound : n + 1 < m + 2 := by omega
                simpa [c, a, i, adjacentHighIndex, hn1_bound] using hhi_lt_nat
              have hrate_lt :
                  binaryEndpointAwareAdjacentRate alt sampleRate i <
                    binaryEndpointAwareAdjacentRate candidate sampleRate i :=
                binaryEndpointAwareAdjacentRate_interior_lt_of_high_strict_shrink
                  sampleRate candidate alt hcandidate halt i hfirst hlast
                  (hsample_high i) (hsample_low i) hlow_le_fin hhi_lt_fin
              have hrate_candidate :
                  binaryEndpointAwareAdjacentRate candidate sampleRate i = r :=
                heq i
              exact
                (not_lt_of_ge ((hrate_candidate.symm ▸ hrate_ge i))) hrate_lt
    have hstrict_exists : ∃ n : ℕ, n ≤ m ∧ c n < a n := by
      by_contra hnone
      apply hne
      funext θ
      have hθ_le : θ.val ≤ m + 1 := Nat.le_of_lt_succ θ.isLt
      by_cases hlastθ : θ.val = m + 1
      · have hθlast : θ = (lastLevelIndex : Fin (m + 2)) := by
          ext
          simpa [lastLevelIndex] using hlastθ
        simpa [hθlast] using halt.2.1.trans hcandidate.2.1.symm
      · have hθ_le_m : θ.val ≤ m := by omega
        have hle : c θ.val ≤ a θ.val := hge_coord θ.val hθ_le_m
        have hnot : ¬ c θ.val < a θ.val := by
          intro hlt
          exact hnone ⟨θ.val, hθ_le_m, hlt⟩
        have hge : a θ.val ≤ c θ.val := le_of_not_gt hnot
        have hθ_bound : θ.val < m + 2 := θ.isLt
        have hca : c θ.val = candidate θ := by
          simpa [c, hθ_bound]
        have haa : a θ.val = alt θ := by
          simpa [a, hθ_bound]
        rw [hca, haa] at hle hge
        exact le_antisymm hge hle
    rcases hstrict_exists with ⟨k, hk_le_m, hk_strict⟩
    have hk_pos : 0 < k := by
      by_contra hk_not
      have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk_not
      subst k
      have h0 : 0 < m + 2 := by omega
      have hc0 : c 0 = 0 := by
        simpa [c, h0, firstLevelIndex] using hcandidate.1
      have ha0 : a 0 = 0 := by
        simpa [a, h0, firstLevelIndex] using halt.1
      rw [hc0, ha0] at hk_strict
      exact (lt_irrefl (0 : ℝ)) hk_strict
    have hprop :
        ∀ n : ℕ, k ≤ n → n ≤ m → c n < a n := by
      intro n hkn hnm
      induction n, hkn using Nat.le_induction with
      | base =>
          exact hk_strict
      | succ n hkn ih =>
          have hn_le_m : n ≤ m := Nat.le_of_lt (Nat.lt_of_succ_le hnm)
          have hn_lt_m : n < m := Nat.lt_of_succ_le hnm
          have hn_lt_adj : n < m + 1 := by omega
          let i : Fin (m + 1) := ⟨n, hn_lt_adj⟩
          have hfirst : i.val ≠ 0 := by
            have hk_le_n : k ≤ n := hkn
            have hk_pos' : 0 < k := hk_pos
            simp [i]
            omega
          have hlast : i.val ≠ m := by
            simp [i]
            omega
          have hlow_lt_fin :
              candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) := by
            have hn_bound : n < m + 2 := by omega
            simpa [c, a, i, adjacentLowIndex, hn_bound] using ih hn_le_m
          by_contra hnot
          have hhi_le_nat : a (n + 1) ≤ c (n + 1) := le_of_not_gt hnot
          have hhi_le_fin :
              alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i) := by
            have hn1_bound : n + 1 < m + 2 := by omega
            simpa [c, a, i, adjacentHighIndex, hn1_bound] using hhi_le_nat
          have hrate_lt :
              binaryEndpointAwareAdjacentRate alt sampleRate i <
                binaryEndpointAwareAdjacentRate candidate sampleRate i :=
            binaryEndpointAwareAdjacentRate_interior_lt_of_low_strict_shrink
              sampleRate candidate alt hcandidate halt i hfirst hlast
              (hsample_high i) (hsample_low i) hlow_lt_fin hhi_le_fin
          have hrate_candidate :
              binaryEndpointAwareAdjacentRate candidate sampleRate i = r :=
            heq i
          exact (not_lt_of_ge ((hrate_candidate.symm ▸ hrate_ge i))) hrate_lt
    have hlast_strict_nat : c m < a m :=
      hprop m (by omega) le_rfl
    have hlast_strict_fin :
        candidate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
          alt (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
      have hm_bound : m < m + 2 := by omega
      simpa [c, a, lastAdjacentIndex, adjacentLowIndex, hm_bound]
        using hlast_strict_nat
    have hlast_rate_lt :
        binaryEndpointAwareAdjacentRate alt sampleRate
            (lastAdjacentIndex : Fin (m + 1)) <
          binaryEndpointAwareAdjacentRate candidate sampleRate
            (lastAdjacentIndex : Fin (m + 1)) :=
      binaryEndpointAwareAdjacentRate_last_lt_of_low_lt
        hm sampleRate candidate alt hcandidate halt
        (hsample_low (lastAdjacentIndex : Fin (m + 1))) hlast_strict_fin
    have hlast_candidate :
        binaryEndpointAwareAdjacentRate candidate sampleRate
            (lastAdjacentIndex : Fin (m + 1)) = r :=
      heq (lastAdjacentIndex : Fin (m + 1))
    exact
      (not_lt_of_ge
        ((hlast_candidate.symm ▸
          hrate_ge (lastAdjacentIndex : Fin (m + 1)))))
        hlast_rate_lt

/--
Finite Lemma 3.1 equivalence, conditional only on the existence of an
equalized endpoint vector: among endpoint-normalized feasible vectors,
maximizing the finite worst-adjacent rate is equivalent to equalizing all
endpoint-aware adjacent rates.
-/
theorem binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_iff_pairwise_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq_candidate :
      BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
        alt ↔
      BinaryEndpointAwareAdjacentRatesEqualize alt sampleRate := by
  rcases heq_candidate.exists_common_rate with ⟨r, hr⟩
  have hstrict :
      AppliedModelingLib.Optimization.IsStrictMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
        candidate :=
    binaryEndpointAwareAdjacentRateObjective_isStrictMaximizerOn_of_equalized
      hm sampleRate candidate hcandidate hsample_high hsample_low hr
  constructor
  · intro hmax_alt
    have halt_eq_candidate :
        alt = candidate :=
      AppliedModelingLib.Optimization.IsStrictMaximizerOn.eq_of_isMaximizerOn
        hstrict hmax_alt
    subst alt
    exact heq_candidate
  · intro heq_alt
    exact
      binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized
        hm sampleRate alt halt hsample_high hsample_low heq_alt

/-- Bernoulli MGF formula for the source binary-rating model. -/
theorem binaryRatingModel_mgf_eq {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    (binaryRatingModel successProb hprob0 hprob1).mgf θ z =
      (1 - successProb θ) + successProb θ * Real.exp z :=
  realBinaryRatingLDPModel_mgf_eq successProb hprob0 hprob1 θ z

/-- Bernoulli log-MGF formula for the source binary-rating model. -/
theorem binaryRatingModel_logMGF_eq {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    (binaryRatingModel successProb hprob0 hprob1).logMGF θ z =
      Real.log ((1 - successProb θ) + successProb θ * Real.exp z) :=
  realBinaryRatingLDPModel_logMGF_eq successProb hprob0 hprob1 θ z

/-- Derivative formula for the source binary-rating log-MGF. -/
theorem binaryRatingModel_logMGF_hasDerivAt {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (binaryRatingModel successProb hprob0 hprob1).logMGF θ t)
      (successProb θ * Real.exp z /
        ((1 - successProb θ) + successProb θ * Real.exp z)) z :=
  realBinaryRatingLDPModel_logMGF_hasDerivAt
    successProb hprob0 hprob1 θ z

/-- Interior binary-model rate function is the source Bernoulli KL formula. -/
theorem binaryRatingModel_rateFunction_eq_sourceBernoulliKL
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (θ : Seller) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).rateFunction θ a =
      sourceBernoulliKL a (successProb θ) :=
  realBinaryRatingLDPModel_rateFunction_eq_bernoulliKL
    successProb hprob0 hprob1 hprob_pos hprob_lt_one θ ha0 ha1

/-- Interior binary-model support-safe rate function is the source Bernoulli KL formula. -/
theorem binaryRatingModel_rateFunctionTop_eq_sourceBernoulliKL
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (θ : Seller) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).rateFunctionTop θ a =
      (sourceBernoulliKL a (successProb θ) : WithTop ℝ) :=
  realBinaryRatingLDPModel_rateFunctionTop_eq_bernoulliKL
    successProb hprob0 hprob1 hprob_pos hprob_lt_one θ ha0 ha1

/--
Interior binary pairwise support-safe rate objective is the source
two-Bernoulli KL threshold rate.
-/
theorem binaryRatingModel_pairwiseRateObjectiveTop_eq_source_threshold_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).pairwiseRateObjectiveTop
        sampleRate hi lo a =
      (twoBernoulliThresholdRate (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) a : WithTop ℝ) :=
  realBinaryRatingLDPModel_pairwiseRateObjectiveTop_eq_twoBernoulliThresholdRate
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate hi lo ha0 ha1

/--
For two interior source binary-rating levels, the support-safe pairwise
threshold rate equals the closed weighted Bernoulli rate.
-/
theorem binaryRatingModel_pairwiseThresholdRateTop_eq_closed_weighted_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hG : sampleRate hi + sampleRate lo ≠ 0) :
    pairwiseSellerThresholdRateTop
        (binaryRatingModel successProb hprob0 hprob1)
        sampleRate hi lo =
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) : WithTop ℝ) :=
  realBinaryRatingLDPModel_pairwiseSellerThresholdRateTop_eq_weightedClosedThresholdRate
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate hi lo hgHi hgLo hG

/--
Interior binary probabilities give the full-support condition needed by the
finite-support pairwise LDP constructors.
-/
theorem binaryRatingModel_fullSupport_of_probabilities_interior
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1) :
    (binaryRatingModel successProb hprob0 hprob1).fullSupport :=
  realBinaryRatingLDPModel_fullSupport_of_pos_lt_one
    successProb hprob0 hprob1 hprob_pos hprob_lt_one

/--
Pairwise LDP certificates for the source binary-rating model from common
log-MGF derivative witnesses. Binary full support and support straddling are
discharged from the interior probability assumptions.
-/
def binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_common_logMGF_derivatives
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairHi p) t)
          (a p) (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairLo p) t)
          (a p) (-(z p * (sampleRate (pairLo p))⁻¹))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
    realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_common_logMGF_derivatives
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a z hz hderiv_hi hderiv_lo

/--
Pairwise LDP certificates for the source binary-rating model from the explicit
Bernoulli derivative equations for the common threshold.
-/
def binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_derivative_formula
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hcommon_hi :
      ∀ p : Pair,
        a p =
          successProb (pairHi p) *
              Real.exp (z p * (sampleRate (pairHi p))⁻¹) /
            ((1 - successProb (pairHi p)) +
              successProb (pairHi p) *
                Real.exp (z p * (sampleRate (pairHi p))⁻¹)))
    (hcommon_lo :
      ∀ p : Pair,
        a p =
          successProb (pairLo p) *
              Real.exp (-(z p * (sampleRate (pairLo p))⁻¹)) /
            ((1 - successProb (pairLo p)) +
              successProb (pairLo p) *
                Real.exp (-(z p * (sampleRate (pairLo p))⁻¹)))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
    realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_derivative_formula
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a z hz hcommon_hi hcommon_lo

/--
Pairwise LDP certificates for the source binary-rating model from a common
interior threshold and the weighted common-dual equation.
-/
def binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_common_threshold_inverse
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a : Pair → ℝ)
    (ha0 : ∀ p : Pair, 0 < a p)
    (ha1 : ∀ p : Pair, a p < 1)
    (hdual_nonpos :
      ∀ p : Pair,
        sampleRate (pairHi p) *
          binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p) ≤ 0)
    (hdual_eq :
      ∀ p : Pair,
        sampleRate (pairHi p) *
            binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p) =
          -(sampleRate (pairLo p) *
            binaryLogMGFDerivativeArg (successProb (pairLo p)) (a p))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_common_threshold_inverse
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a ha0 ha1 hdual_nonpos hdual_eq

/--
Pairwise LDP certificates for the source binary-rating model from a common
interior threshold, weighted common-dual equation, and the source-shaped
ordering condition that the threshold lies weakly below the high type's
success probability.
-/
def binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_ordered_common_threshold_inverse
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a : Pair → ℝ)
    (ha0 : ∀ p : Pair, 0 < a p)
    (ha1 : ∀ p : Pair, a p < 1)
    (ha_le_hi : ∀ p : Pair, a p ≤ successProb (pairHi p))
    (hdual_eq :
      ∀ p : Pair,
        sampleRate (pairHi p) *
            binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p) =
          -(sampleRate (pairLo p) *
            binaryLogMGFDerivativeArg (successProb (pairLo p)) (a p))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_ordered_common_threshold_inverse
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a ha0 ha1 ha_le_hi hdual_eq

/--
Pairwise LDP certificates for the source binary-rating model from the weighted
geometric common threshold. The threshold interior and dual-balance equations
are discharged by the shared binary library.
-/
def binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_weighted_common_threshold
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (hG :
      ∀ p : Pair,
        sampleRate (pairHi p) + sampleRate (pairLo p) ≠ 0)
    (ha_le_hi :
      ∀ p : Pair,
        weightedBernoulliCommonThreshold
            (sampleRate (pairHi p)) (sampleRate (pairLo p))
            (successProb (pairHi p)) (successProb (pairLo p)) ≤
          successProb (pairHi p)) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_weighted_common_threshold
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo hG ha_le_hi

/--
Endpoint binary left-tail certificate for the first adjacent interval: if the
low type has success probability zero, the two-sample comparison error has the
high type's zero-success tail rate scaled by the high sampling rate.
-/
theorem binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_low_success_zero
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi)
    (hpHi0 : 0 < successProb hi)
    (hpHi1 : successProb hi < 1)
    (hpLo_zero : successProb lo = 0) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
      (sampleRate hi * (-Real.log (1 - successProb hi))) := by
  refine
    twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_lo_scores_zero
      (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo hgHi
      ?_ ?_ (pZero := 1 - successProb hi) ?_ (sub_pos.mpr hpHi1) ?_
  · intro r _hmass
    cases r <;> simp [binaryRatingModel, realBinaryRatingLDPModel,
      binaryRatingScore]
  · intro r
    cases r <;> simp [binaryRatingModel, realBinaryRatingLDPModel,
      binaryRatingScore]
  · simpa [binaryRatingModel, realBinaryRatingLDPModel] using
      realBernoulliPMF_binaryRatingScore_zero_prob
        (successProb hi) (hprob0 hi) (hprob1 hi)
  · have hlo_zero :=
      realBernoulliPMF_binaryRatingScore_zero_prob
        (successProb lo) (hprob0 lo) (hprob1 lo)
    have hzero_rhs : 1 - successProb lo = 1 := by
      rw [hpLo_zero]
      norm_num
    simpa [binaryRatingModel, realBinaryRatingLDPModel, hzero_rhs] using
      hlo_zero

/--
Endpoint binary left-tail certificate for the last adjacent interval: if the
high type has success probability one, the two-sample comparison error has the
low type's success-tail rate scaled by the low sampling rate.
-/
theorem binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_high_success_one
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi)
    (hgLo : 0 < sampleRate lo)
    (hpHi_one : successProb hi = 1)
    (hpLo0 : 0 < successProb lo)
    (hpLo1 : successProb lo < 1) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
      (sampleRate lo * (-Real.log (successProb lo))) := by
  refine
    twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_hi_scores_one
      (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo
      hgHi hgLo ?_ (pOne := successProb lo) ?_ hpLo0 ?_
  · intro r
    cases r <;> simp [binaryRatingModel, realBinaryRatingLDPModel,
      binaryRatingScore]
  · simpa [binaryRatingModel, realBinaryRatingLDPModel] using
      realBernoulliPMF_one_sub_binaryRatingScore_zero_prob
        (successProb lo) (hprob0 lo) (hprob1 lo)
  · have hhi_one :=
      realBernoulliPMF_one_sub_binaryRatingScore_zero_prob
        (successProb hi) (hprob0 hi) (hprob1 hi)
    have hone_rhs : successProb hi = 1 := hpHi_one
    simpa [binaryRatingModel, realBinaryRatingLDPModel, hone_rhs] using
      hhi_one

/--
Interior adjacent-pair binary left-tail certificate at the closed weighted
Bernoulli rate.  This pair-local theorem is the middle-interval companion to
the two endpoint certificates above.
-/
theorem binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi) (hpHi1 : successProb hi < 1)
    (hpLo0 : 0 < successProb lo) (hpLo1 : successProb lo < 1)
    (hpLo_le_hi : successProb lo ≤ successProb hi) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo)) :=
  realBinaryRatingLDPModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
    successProb hprob0 hprob1 sampleRate hi lo hgHi hgLo
    hpHi0 hpHi1 hpLo0 hpLo1 hpLo_le_hi

/--
Interior pairwise `1 - P_k` certificate for the source binary-rating model at
the closed weighted Bernoulli rate.  This is the pointwise C.4 kernel
certificate for continuum pairs away from the endpoint atoms.
-/
theorem binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi) (hpHi1 : successProb hi < 1)
    (hpLo0 : 0 < successProb lo) (hpLo1 : successProb lo < 1)
    (hpLo_le_hi : successProb lo ≤ successProb hi) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo)) := by
  simpa [binaryRatingModel] using
    realBinaryRatingLDPModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
      successProb hprob0 hprob1 sampleRate hi lo hgHi hgLo
      hpHi0 hpHi1 hpLo0 hpLo1 hpLo_le_hi

/--
Theorem 3.1 Part 1 asymptotic-value bridge.  In the source proof, bounded
convergence sends the weighted success integral
`∫ w(x) P_k(x) dx` to `∫ w(x) dx` when the pairwise success probabilities
`P_k(x)` converge to one.  The hypotheses here isolate the measure-theoretic
bounded-convergence obligations from the rating-specific probability proof.
-/
theorem theorem31_asymptotic_value_integral_tendsto_of_success_prob_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → ℝ) (P : ℕ → Ω → ℝ) {B : ℝ}
    (hprod_meas :
      ∀ k, AEStronglyMeasurable (fun x => w x * P k x) μ)
    (hprod_bound :
      ∀ k, ∀ᵐ x ∂μ, 0 ≤ w x * P k x ∧ w x * P k x ≤ B)
    (hP_lim : ∀ᵐ x ∂μ, Tendsto (fun k => P k x) atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x, w x * P k x ∂μ)
      atTop (𝓝 (∫ x, w x ∂μ)) :=
  AppliedModelingLib.Math.tendsto_integral_mul_tendsto_one_of_nonneg_le_const
    μ w P hprod_meas hprod_bound hP_lim

/--
Theorem 3.1 Part 1 binary floor-objective bridge.  For the paper's binary
`P_k` objective, product measurability follows from measurable success and
sample-rate functions, while domination follows from `|P_k| ≤ 1` and a bounded
weight.  The remaining model-specific input is the source probability result
that `P_k(q)` tends to one almost everywhere.
-/
theorem theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_tendsto_one
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (w : ℝ × ℝ → ℝ) {B : ℝ}
    (hw_meas : AEStronglyMeasurable w μ)
    (hw_bound : ∀ᵐ q ∂μ, ‖w q‖ ≤ B)
    (hP_lim :
      ∀ᵐ q ∂μ,
        Tendsto
          (fun k : ℕ =>
            twoSampleFloorPkObjectiveProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k)
          atTop (𝓝 1)) :
    Tendsto
      (fun k : ℕ =>
        ∫ q,
          w q *
            twoSampleFloorPkObjectiveProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k ∂μ)
      atTop (𝓝 (∫ q, w q ∂μ)) := by
  let M := binaryRatingModel successProb hprob0 hprob1
  refine
    AppliedModelingLib.Math.tendsto_integral_mul_tendsto_one_of_weight_norm_bound_of_factor_norm_le_one
      μ w
      (fun k : ℕ => fun q : ℝ × ℝ =>
        twoSampleFloorPkObjectiveProb M sampleRate q.1 q.2 k)
      ?_ hw_bound ?_ ?_
  · intro k
    have hP_meas :
        AEStronglyMeasurable
          (fun q : ℝ × ℝ =>
            twoSampleFloorPkObjectiveProb M sampleRate q.1 q.2 k) μ := by
      simpa [M, binaryRatingModel] using
        realBinaryRatingLDPModel_twoSampleFloorPkObjectiveProb_aestronglyMeasurable
          μ successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
    exact hw_meas.mul hP_meas
  · intro k
    filter_upwards with q
    simpa [Real.norm_eq_abs, M] using
      twoSampleFloorPkObjectiveProb_abs_le_one M sampleRate q.1 q.2 k
  · simpa [M] using hP_lim

/--
Theorem 3.1 Part 1 binary floor-objective bridge from positive exponential
decay of the pairwise complement error.  This packages the source large
deviation input into the bounded-convergence asymptotic-value statement: if
`1 - P_k(q)` has a positive exponential-rate certificate almost everywhere,
then the weighted floor-objective integral converges to its limiting weighted
value.
-/
theorem theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_positive_rate
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (w : ℝ × ℝ → ℝ) {B : ℝ}
    (hw_meas : AEStronglyMeasurable w μ)
    (hw_bound : ∀ᵐ q ∂μ, ‖w q‖ ≤ B)
    (hcert_ae :
      ∀ᵐ q ∂μ,
        ∃ rate : ℝ, 0 < rate ∧
          ExponentialRateCertificate
            (fun k : ℕ =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel successProb hprob0 hprob1) sampleRate
                q.1 q.2 k)
            rate) :
    Tendsto
      (fun k : ℕ =>
        ∫ q,
          w q *
            twoSampleFloorPkObjectiveProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k ∂μ)
      atTop (𝓝 (∫ q, w q ∂μ)) := by
  let M := binaryRatingModel successProb hprob0 hprob1
  refine
    theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_tendsto_one
      μ successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas
      w hw_meas hw_bound ?_
  filter_upwards [hcert_ae] with q hq
  rcases hq with ⟨rate, hrate, hcert⟩
  have hcert_one_sub :
      ExponentialRateCertificate
        (fun k : ℕ =>
          1 - twoSampleFloorPkObjectiveProb M sampleRate q.1 q.2 k)
        rate := by
    refine ExponentialRateCertificate.congr ?_ hcert
    filter_upwards with k
    exact
      (twoSampleFloorPkComplementErrorProb_eq_one_sub_pkObjectiveProb
        M sampleRate q.1 q.2 k).symm
  simpa [M] using hcert_one_sub.tendsto_one_of_one_sub_pos_rate hrate

/--
Theorem 3.1 Part 1 binary floor-objective bridge from a uniform
exponential-rate certificate on an almost-sure support set.  This is the
continuum-facing version of the positive-rate bridge: compact-uniform
large-deviation certificates can be restricted pointwise on the a.e. support.
-/
theorem theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_uniform_positive_rate_on
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (w : ℝ × ℝ → ℝ) {B : ℝ}
    (hw_meas : AEStronglyMeasurable w μ)
    (hw_bound : ∀ᵐ q ∂μ, ‖w q‖ ≤ B)
    {certSet : Set (ℝ × ℝ)} {rate : ℝ × ℝ → ℝ}
    (hmem_ae : ∀ᵐ q ∂μ, q ∈ certSet)
    (hrate_pos_on : ∀ q, q ∈ certSet → 0 < rate q)
    (hcert :
      UniformExponentialRateCertificateOn
        (fun k : ℕ => fun q : ℝ × ℝ =>
          twoSampleFloorPkComplementErrorProb
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            q.1 q.2 k)
        rate certSet) :
    Tendsto
      (fun k : ℕ =>
        ∫ q,
          w q *
            twoSampleFloorPkObjectiveProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k ∂μ)
      atTop (𝓝 (∫ q, w q ∂μ)) := by
  refine
    theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_positive_rate
      μ successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas
      w hw_meas hw_bound ?_
  filter_upwards [hmem_ae] with q hq
  exact ⟨rate q, hrate_pos_on q hq, hcert.toExponentialRateCertificate hq⟩

/--
Theorem 3.1 Part 1 binary floor-objective bridge for ordered interior pairs.
If almost every comparison pair has positive sample rates and strictly ordered
interior success probabilities, the pointwise Bernoulli large-deviation
certificate supplies the positive-rate hypothesis needed for asymptotic value
convergence.
-/
theorem theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_ordered_interior
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (w : ℝ × ℝ → ℝ) {B : ℝ}
    (hw_meas : AEStronglyMeasurable w μ)
    (hw_bound : ∀ᵐ q ∂μ, ‖w q‖ ≤ B)
    (hordered_ae :
      ∀ᵐ q ∂μ,
        0 < sampleRate q.1 ∧ 0 < sampleRate q.2 ∧
          0 < successProb q.2 ∧
          successProb q.2 < successProb q.1 ∧
          successProb q.1 < 1) :
    Tendsto
      (fun k : ℕ =>
        ∫ q,
          w q *
            twoSampleFloorPkObjectiveProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              q.1 q.2 k ∂μ)
      atTop (𝓝 (∫ q, w q ∂μ)) := by
  refine
    theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_positive_rate
      μ successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas
      w hw_meas hw_bound ?_
  filter_upwards [hordered_ae] with q hq
  rcases hq with ⟨hgHi, hgLo, hpLo0, hpLo_lt_hi, hpHi1⟩
  refine
    ⟨weightedBernoulliClosedThresholdRate
        (sampleRate q.1) (sampleRate q.2)
        (successProb q.1) (successProb q.2),
      ?_, ?_⟩
  · exact
      weightedBernoulliClosedThresholdRate_pos_of_lt
        hgHi hgLo hpLo0 hpLo_lt_hi hpHi1
  · exact
      binaryRatingModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate q.1 q.2 hgHi hgLo
        (hpLo0.trans hpLo_lt_hi) hpHi1 hpLo0
        (hpLo_lt_hi.trans hpHi1) hpLo_lt_hi.le

/--
Theorem 3.1 two-stage optimality logic.  If a candidate maximizes the limiting
value objective and no feasible design with that same limiting value has a
larger large-deviation rate, then it is lexicographically optimal for the
source criterion: asymptotic value first, convergence rate second.
-/
theorem theorem31_two_stage_lexicographic_optimality
    {Design : Type*} (feasible : Design → Prop)
    (limitingValue rate : Design → ℝ) (candidate : Design)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn feasible limitingValue candidate)
    (hrate :
      ∀ alternative, feasible alternative →
        limitingValue alternative = limitingValue candidate →
          rate alternative ≤ rate candidate) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      feasible limitingValue rate candidate :=
  AppliedModelingLib.Optimization.isLexicographicMaximizerOn_of_primary_and_secondary_on_tie
    hvalue hrate

/--
Theorem 3.1 two-stage source form.  If the candidate maximizes the limiting
value objective and also maximizes the large-deviation rate among designs with
that same limiting value, then it is optimal for the paper's lexicographic
"asymptotic value first, rate second" criterion.
-/
theorem theorem31_two_stage_lexicographic_optimality_of_rate_maximizer_on_value_fiber
    {Design : Type*} (feasible : Design → Prop)
    (limitingValue rate : Design → ℝ) (candidate : Design)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn feasible limitingValue candidate)
    (hrate :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (fun alternative =>
          feasible alternative ∧
            limitingValue alternative = limitingValue candidate)
        rate candidate) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      feasible limitingValue rate candidate :=
  AppliedModelingLib.Optimization.isLexicographicMaximizerOn_of_primary_and_secondary_maximizer_on_tie
    hvalue hrate

/--
Theorem 3.1 two-stage partition/endpoint source form.  A partition `Sstar`
maximizes the limiting value, and the endpoint levels `tstar` dominate the
large-deviation rate on the whole value-maximizing fiber.  This is the exact
source-level composition needed for the continuum `S*` layer: optimizing
levels for a fixed partition is enough only after ties between value-optimal
partitions have been handled.
-/
theorem theorem31_partition_endpoint_two_stage_lexicographic_optimality
    {Partition Endpoint : Type*}
    (partitionFeasible : Partition → Prop)
    (endpointFeasible : Partition → Endpoint → Prop)
    (limitingValue : Partition → ℝ)
    (rate : Partition → Endpoint → ℝ)
    (Sstar : Partition) (tstar : Endpoint)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn partitionFeasible limitingValue
        Sstar)
    (htstar : endpointFeasible Sstar tstar)
    (hrate :
      ∀ S t, partitionFeasible S → endpointFeasible S t →
        limitingValue S = limitingValue Sstar →
          rate S t ≤ rate Sstar tstar) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : Partition × Endpoint =>
        partitionFeasible design.1 ∧ endpointFeasible design.1 design.2)
      (fun design : Partition × Endpoint => limitingValue design.1)
      (fun design : Partition × Endpoint => rate design.1 design.2)
      (Sstar, tstar) := by
  refine
    theorem31_two_stage_lexicographic_optimality
      (fun design : Partition × Endpoint =>
        partitionFeasible design.1 ∧ endpointFeasible design.1 design.2)
      (fun design : Partition × Endpoint => limitingValue design.1)
      (fun design : Partition × Endpoint => rate design.1 design.2)
      (Sstar, tstar) ?_ ?_
  · exact ⟨⟨hvalue.isFeasible, htstar⟩, fun design hdesign =>
      hvalue.le hdesign.1⟩
  · intro design hdesign hsame
    exact hrate design.1 design.2 hdesign.1 hdesign.2 hsame

/--
Theorem 3.1 two-stage source form with a unique primary optimizer.  If the
limiting-value maximizing partition is unique, then the endpoint optimizer for
that single partition suffices for full lexicographic optimality: every other
partition has strictly smaller primary value, and ties can only occur at
`Sstar`.
-/
theorem theorem31_partition_endpoint_two_stage_lexicographic_optimality_of_unique_value_argmax
    {Partition Endpoint : Type*}
    (partitionFeasible : Partition → Prop)
    (endpointFeasible : Partition → Endpoint → Prop)
    (limitingValue : Partition → ℝ)
    (rate : Partition → Endpoint → ℝ)
    (Sstar : Partition) (tstar : Endpoint)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn partitionFeasible limitingValue
        Sstar)
    (hvalue_unique :
      ∀ S, partitionFeasible S →
        limitingValue S = limitingValue Sstar → S = Sstar)
    (htstar :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (endpointFeasible Sstar) (rate Sstar) tstar) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : Partition × Endpoint =>
        partitionFeasible design.1 ∧ endpointFeasible design.1 design.2)
      (fun design : Partition × Endpoint => limitingValue design.1)
      (fun design : Partition × Endpoint => rate design.1 design.2)
      (Sstar, tstar) :=
  theorem31_partition_endpoint_two_stage_lexicographic_optimality
    partitionFeasible endpointFeasible limitingValue rate Sstar tstar
    hvalue htstar.isFeasible
    (by
      intro S t hS ht heq
      have hS_eq : S = Sstar := hvalue_unique S hS heq
      subst S
      exact htstar.le ht)

/--
Compact-domain existence form of Theorem 3.1's two-stage optimization
argument. If the feasible partition set is compact and the limiting value is
continuous on it, then an `Sstar` maximizer exists; if the endpoint
construction supplies a secondary-rate optimizer on the limiting-value tie
fiber, the combined partition/endpoint design is lexicographically optimal.
-/
theorem theorem31_exists_partition_endpoint_two_stage_lexicographic_optimality_of_isCompact_continuousOn
    {Partition Endpoint : Type*} [TopologicalSpace Partition]
    (partitionSet : Set Partition)
    (endpointFeasible : Partition → Endpoint → Prop)
    (limitingValue : Partition → ℝ)
    (rate : Partition → Endpoint → ℝ)
    (hcompact : IsCompact partitionSet)
    (hnonempty : partitionSet.Nonempty)
    (hcontinuous : ContinuousOn limitingValue partitionSet)
    (hendpoint :
      ∀ Sstar : Partition, Sstar ∈ partitionSet →
        ∃ tstar : Endpoint,
          endpointFeasible Sstar tstar ∧
            ∀ S t, S ∈ partitionSet → endpointFeasible S t →
              limitingValue S = limitingValue Sstar →
                rate S t ≤ rate Sstar tstar) :
    ∃ design : Partition × Endpoint,
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : Partition × Endpoint =>
          design.1 ∈ partitionSet ∧ endpointFeasible design.1 design.2)
        (fun design : Partition × Endpoint => limitingValue design.1)
        (fun design : Partition × Endpoint => rate design.1 design.2)
        design := by
  rcases
    AppliedModelingLib.Optimization.exists_isMaximizerOn_of_isCompact_continuousOn
      hcompact hnonempty limitingValue hcontinuous with
    ⟨Sstar, hSstar⟩
  rcases hendpoint Sstar hSstar.isFeasible with
    ⟨tstar, htstar, hrate⟩
  refine ⟨(Sstar, tstar), ?_⟩
  exact
    theorem31_partition_endpoint_two_stage_lexicographic_optimality
      (fun S : Partition => S ∈ partitionSet)
      endpointFeasible limitingValue rate Sstar tstar hSstar htstar hrate

/--
Finite-gap version of the compact-domain Theorem 3.1 optimizer.  A continuous
limiting-value objective on the finite probability simplex of interval gaps
attains a maximizing gap vector; if the endpoint construction solves the
secondary rate problem on the resulting value-maximizing fiber, the combined
gap/endpoint design is lexicographically optimal.
-/
theorem theorem31_exists_gap_partition_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex
    {M : ℕ} [Nonempty (Fin M)] {Endpoint : Type*}
    (endpointFeasible : (Fin M → ℝ) → Endpoint → Prop)
    (limitingValue : (Fin M → ℝ) → ℝ)
    (rate : (Fin M → ℝ) → Endpoint → ℝ)
    (hcontinuous :
      ContinuousOn limitingValue
        {gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
    (hendpoint :
      ∀ gap : Fin M → ℝ, AppliedModelingLib.FiniteProbabilitySimplex gap →
        ∃ tstar : Endpoint,
          endpointFeasible gap tstar ∧
            ∀ otherGap t, AppliedModelingLib.FiniteProbabilitySimplex otherGap →
              endpointFeasible otherGap t →
                limitingValue otherGap = limitingValue gap →
                  rate otherGap t ≤ rate gap tstar) :
    ∃ design : (Fin M → ℝ) × Endpoint,
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (Fin M → ℝ) × Endpoint =>
          AppliedModelingLib.FiniteProbabilitySimplex design.1 ∧
            endpointFeasible design.1 design.2)
        (fun design : (Fin M → ℝ) × Endpoint => limitingValue design.1)
        (fun design : (Fin M → ℝ) × Endpoint => rate design.1 design.2)
        design := by
  exact
    theorem31_exists_partition_endpoint_two_stage_lexicographic_optimality_of_isCompact_continuousOn
      ({gap : Fin M → ℝ | AppliedModelingLib.FiniteProbabilitySimplex gap})
      endpointFeasible limitingValue rate
      AppliedModelingLib.finiteProbabilitySimplex_isCompact
      AppliedModelingLib.finiteProbabilitySimplex_nonempty
      hcontinuous
      (by
        intro gap hgap
        exact hendpoint gap hgap)

/--
Theorem C.1 upper-bound bridge.  If the integrated error kernel is
nonnegative and has an almost-everywhere exponential envelope whose pointwise
rate is at least `targetRate`, then the weighted integral has exponential
upper bound `targetRate`.

This is the reusable upper-bound half of the source Laplace-principle step;
the matching lower bound requires the compact near-minimizer/positive-measure
argument.
-/
theorem theoremC1_integral_error_upper_bound_from_rate_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (errorKernel : ℕ → Ω → ℝ) (rateFunction : Ω → ℝ)
    {targetRate C : ℝ}
    (hCpos : 0 < C)
    (herror_meas :
      ∀ k, AEStronglyMeasurable (errorKernel k) μ)
    (hrate :
      ∀ᵐ x ∂μ, targetRate ≤ rateFunction x)
    (herror_bound :
      ∀ k, ∀ᵐ x ∂μ,
        0 ≤ errorKernel k x ∧
          errorKernel k x ≤
            C * Real.exp (-(k : ℝ) * rateFunction x)) :
    HasExpUpperBoundWithConst
      (fun k : ℕ => ∫ x, errorKernel k x ∂μ)
      targetRate :=
  integral_hasExpUpperBoundWithConst_of_ae_rate_envelope
    μ hCpos herror_meas hrate herror_bound

/--
Theorem C.1 lower-bound near-minimizer bridge.  If a positive-measure set has
a uniform exponential lower envelope, then the set integral has the
corresponding exponential lower bound.

This isolates the positive-measure near-minimizer step used in the lower-bound
half of the source Laplace principle.
-/
theorem theoremC1_setIntegral_error_lower_bound_from_near_minimizer_set
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {nearMinimizers : Set Ω}
    (errorKernel : ℕ → Ω → ℝ)
    {rate c : ℝ}
    (hmeasure_pos : 0 < μ.real nearMinimizers)
    (hcpos : 0 < c)
    (herror_int :
      ∀ k, IntegrableOn (errorKernel k) nearMinimizers μ)
    (hlower :
      ∀ᶠ k : ℕ in atTop, ∀ᵐ x ∂μ.restrict nearMinimizers,
        c * Real.exp (-(k : ℝ) * rate) ≤ errorKernel k x) :
    HasExpLowerBoundWithConst
      (fun k : ℕ => ∫ x in nearMinimizers, errorKernel k x ∂μ)
      rate :=
  setIntegral_hasExpLowerBoundWithConst_of_ae_const_exp_le
    μ hmeasure_pos hcpos herror_int hlower

/--
Theorem C.1 exact-rate skeleton.  A pointwise exponential upper-rate envelope
together with positive-measure near-minimizer lower sets for every rate above
`rate` implies that the integrated error has exponential decay rate `rate`.

The remaining paper-specific work for the full source theorem is to construct
those near-minimizer sets from the compact essential-infimum and uniform
convergence hypotheses.
-/
theorem theoremC1_integral_error_exponential_rate_from_rate_envelope_and_near_minimizer_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (errorKernel : ℕ → Ω → ℝ) (rateFunction : Ω → ℝ)
    {rate C : ℝ}
    (hCpos : 0 < C)
    (herror_meas :
      ∀ k, AEStronglyMeasurable (errorKernel k) μ)
    (herror_int :
      ∀ k, Integrable (errorKernel k) μ)
    (hrate :
      ∀ᵐ x ∂μ, rate ≤ rateFunction x)
    (hupper_envelope :
      ∀ k, ∀ᵐ x ∂μ,
        0 ≤ errorKernel k x ∧
          errorKernel k x ≤
            C * Real.exp (-(k : ℝ) * rateFunction x))
    (hlower_sets : ∀ targetRate, rate < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ,
        0 < μ.real nearMinimizers ∧ 0 < c ∧
          (∀ k, IntegrableOn (errorKernel k) nearMinimizers μ) ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ᵐ x ∂μ.restrict nearMinimizers,
                c * Real.exp (-(k : ℝ) * targetRate) ≤ errorKernel k x) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, errorKernel k x ∂μ)
      rate :=
  integral_hasExponentialRate_of_ae_rate_envelope_and_setLowerBounds
    μ hCpos herror_meas herror_int hrate hupper_envelope hlower_sets

/--
Theorem C.1 zero-rate skeleton.  For the reverse branch, a fixed upper bound
on the nonnegative integrated error and positive-measure local lower envelopes
at every positive target rate force exact exponential rate zero.
-/
theorem theoremC1_integral_error_zero_rate_from_constant_upper_bound_and_near_minimizer_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (errorKernel : ℕ → Ω → ℝ) {B : ℝ}
    (hBpos : 0 < B)
    (herror_int : ∀ k, Integrable (errorKernel k) μ)
    (herror_nonneg : ∀ k, ∀ᵐ x ∂μ, 0 ≤ errorKernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop, (∫ x, errorKernel k x ∂μ) ≤ B)
    (hlower_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ,
        0 < μ.real nearMinimizers ∧ 0 < c ∧
          (∀ k, IntegrableOn (errorKernel k) nearMinimizers μ) ∧
            ∀ᶠ k : ℕ in atTop,
              ∀ᵐ x ∂μ.restrict nearMinimizers,
                c * Real.exp (-(k : ℝ) * targetRate) ≤ errorKernel k x) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, errorKernel k x ∂μ)
      0 :=
  integral_hasExponentialRate_zero_of_eventually_le_const_and_setLowerBounds
    μ hBpos herror_int herror_nonneg hupper_const hlower_sets

/--
Theorem C.1 weighted-kernel zero-rate skeleton from a source-style
normalized-log certificate.  The remaining caller work is to provide
positive-measure near-rate sets where the limiting rate is strictly below each
positive target rate and the weight is locally bounded below.
-/
theorem theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_nearRate_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {certSet : Set Ω} {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, Integrable (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop, (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            nearMinimizers ⊆ certSet ∧
              (∀ k : ℕ,
                IntegrableOn
                  (fun x : Ω => weight x * kernel k x)
                  nearMinimizers μ) ∧
                (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                  ∀ x : Ω, x ∈ nearMinimizers →
                    rate x + δ ≤ targetRate) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_nearRate_sets
    μ hBpos hkernel_int hkernel_nonneg hupper_const hcert hnear_sets

/--
Theorem C.1 weighted-kernel zero-rate skeleton from pointwise exponential-rate
certificates on positive-measure near-rate sets.  This is the source-shaped
version used when the pairwise binary LDP is available pointwise but no compact
uniform normalized-log estimate has been proved.
-/
theorem theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_pointwiseExponentialRateCertificate_nearRate_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, Integrable (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop, (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hkernel_meas : ∀ k : ℕ, Measurable (kernel k))
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ k : ℕ,
              IntegrableOn
                (fun x : Ω => weight x * kernel k x)
                nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : Ω, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  ∀ x : Ω, x ∈ nearMinimizers →
                    ExponentialRateCertificate
                      (fun k : ℕ => kernel k x) (rate x)) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_pointwiseExponentialRateCertificate_nearRate_sets
    μ hBpos hkernel_int hkernel_nonneg hupper_const hkernel_meas
    hnear_sets

/--
Theorem C.1 weighted-kernel zero-rate skeleton from a source-style
normalized-log certificate and the weighted near-essential-infimum interface
at rate zero.  This packages the local near-minimizer construction used by
Laplace-principle reverse branches.
-/
theorem theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, Integrable (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop, (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel rate Set.univ)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_weightedNearInf
    μ hBpos hkernel_int hkernel_nonneg hupper_const hcert hweighted_near

/--
Theorem C.1 weighted-kernel zero-rate skeleton from a source-style
normalized-log certificate on a set that contains the integration measure
almost everywhere, plus the weighted near-essential-infimum interface at rate
zero.
-/
theorem theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {certSet : Set Ω} {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, Integrable (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in atTop, (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  weightedKernelIntegral_hasExponentialRate_zero_of_eventually_le_const_and_uniformNormalizedLogRateCertificateOn_weightedNearInf_of_ae_mem_certSet
    μ hBpos hkernel_int hkernel_nonneg hupper_const hcert hcertSet_ae
    hweighted_near

/--
Theorem C.1 Laplace-principle skeleton in the source notation.  If
`phiSeq k` converges uniformly to `phi`, `rate` is an almost-everywhere lower
bound for `phi`, and every `rate + ε` sublevel has positive measure in the
near-infimum restricted-set sense, then the integral of
`exp (-(k : ℝ) * phiSeq k x)` has exponential decay rate `rate`.

This captures the main reusable analytic core of Theorem C.1.  A later
paper-specific wrapper can derive the near-infimum-set hypothesis from a
chosen formal essential-infimum convention.
-/
theorem theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_nearInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ) {rate : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hphi_lower : ∀ᵐ x ∂μ, rate ≤ phi x)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε)
    (hnear : ∀ ε > 0,
      ∃ nearMinimizers : Set Ω,
        0 < μ.real nearMinimizers ∧
          ∀ᵐ x ∂μ.restrict nearMinimizers, phi x ≤ rate + ε) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  laplaceIntegral_hasExponentialRate_of_uniform_tendsto_nearInf
    μ phiSeq phi hintegrable hphi_lower huniform hnear

/--
Theorem C.1 Laplace-principle skeleton in source-style essential-infimum
notation.  If `phiSeq k` converges uniformly to `phi`, `rate` is the
almost-everywhere essential infimum of `phi` in the reusable real-valued
interface, then the integral of `exp (-(k : ℝ) * phiSeq k x)` has exponential
decay rate `rate`.
-/
theorem theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_essentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ) {rate : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  laplaceIntegral_hasExponentialRate_of_uniform_tendsto_essentialInf
    μ phiSeq phi hintegrable hess huniform

/--
Weighted Theorem C.1 Laplace-principle skeleton in source-style notation.  This
matches the paper's weighted pairwise-error objectives: bounded nonnegative
weights preserve the exponential rate when every near-essential-minimizer
region contains a positive-measure subset where the weight is bounded below.
-/
theorem theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_weightedEssentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_hasExponentialRate_of_uniform_tendsto_weightedEssentialInf
    μ weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    hess hweighted_near huniform

/--
Certificate form of the weighted Theorem C.1 Laplace-principle skeleton.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    μ weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    hess hweighted_near huniform

/--
Positive-kernel Theorem C.1 certificate in source-style notation.  This is the
form used when the integrand is a pairwise error probability whose normalized
negative log converges uniformly to the limiting rate function.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ, Integrable (fun x : Ω => weight x * kernel k x) μ)
    (hweight_int : Integrable weight μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight phi rate)
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    μ weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound hess hweighted_near hkernel_pos huniform_log

/--
Positive-kernel Theorem C.1 certificate for continuous limiting rates.  A
global continuous minimizer and uniformly positive objective weight supply the
source-style essential-infimum and positive-near-minimum certificates.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hkernel_int :
      ∀ k : ℕ, Integrable (fun x : Ω => weight x * kernel k x) μ)
    (hweight_int : Integrable weight μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_uniformWeightLower
    μ weight kernel phi hkernel_int hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hkernel_pos huniform_log

/--
Positive-kernel Theorem C.1 certificate for continuous limiting rates with a
source-natural local weight condition.  A global continuous minimizer and an
objective weight that is continuous and positive at that minimizer supply the
positive-near-minimum certificate; no global positive lower bound on the weight
is required.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ, Integrable (fun x : Ω => weight x * kernel k x) μ)
    (hweight_int : Integrable weight μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_weight_pos
    μ weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hkernel_pos huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate for continuous limiting
rates.  This is the component form used after splitting a continuum objective
into measurable interval-pair cells.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_uniformWeightLower
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hlocal_pos hkernel_pos
    huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate with a continuous
positive weight at the cell minimizer, avoiding a cell-wide positive lower bound.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_weight_pos
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hlocal_pos hkernel_pos huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate where local positive
cell mass follows from closure/interior support.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior cell))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_uniformWeightLower
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hclosure hkernel_pos
    huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate with a continuous
positive weight at a closure/interior-supported cell minimizer.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_weight_pos
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos hclosure
    hkernel_pos huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate with a continuous
positive weight at a closure/interior-supported cell minimizer, where
normalized-log convergence is only required on the restricted cell.
-/
theorem theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_on_restrict_closure_interior_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ,
        Integrable (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, x ∈ cell →
          |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  weightedKernelIntegral_exponentialRateCertificate_of_uniform_logRate_tendsto_on_restrict_closure_interior_weight_pos
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos hclosure
    hkernel_pos huniform_log_on

/--
Weighted Theorem C.1 certificate in the paper's source shape
`exp (-k * phiSeq k x)`: uniform convergence of `phiSeq` to a continuous
limiting rate with a global minimizer gives the weighted integral exponent.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_continuous_min_uniformWeightLower
    μ weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont huniform

/--
Weighted Theorem C.1 certificate in the paper's source shape with a continuous
positive weight at the minimizer instead of a global positive lower bound.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_continuous_min_weight_pos
    μ weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos huniform

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate, using an
explicit positive-mass condition around the cell minimizer.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_uniformWeightLower
    μ hcell weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hlocal_pos huniform

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate with a continuous
positive weight at the cell minimizer instead of a cell-wide positive lower bound.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_weight_pos
    μ hcell weight phiSeq phi hintegrable hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hlocal_pos huniform

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate where local
positive cell mass follows from closure/interior support.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior cell))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_uniformWeightLower
    μ hcell weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hclosure huniform

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate with a continuous
positive weight at a closure/interior-supported cell minimizer.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_weight_pos
    μ hcell weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos hclosure huniform

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate with uniform
convergence required only on the restricted cell.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, x ∈ cell → |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_uniformWeightLower
    μ hcell weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hlocal_pos huniform_on

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate with local
positive weight and uniform convergence required only on the restricted cell.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, x ∈ cell → |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_weight_pos
    μ hcell weight phiSeq phi hintegrable hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hlocal_pos huniform_on

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate with
closure/interior support and uniform convergence required only on the
restricted cell.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior cell))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, x ∈ cell → |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_uniformWeightLower
    μ hcell weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hclosure huniform_on

/--
Restricted-cell source-shaped weighted Theorem C.1 certificate with local
positive weight, closure/interior support, and uniform convergence required
only on the restricted cell.
-/
theorem theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell))
    (huniform_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, x ∈ cell → |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  weightedLaplaceIntegral_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_weight_pos
    μ hcell weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos hclosure
    huniform_on

/--
Exact-exponential Theorem C.1 certificate for continuous limiting rates.  This
is the source-shaped `exp (-k * phi x)` specialization of the weighted Laplace
principle, avoiding a separate normalized-log convergence hypothesis.
-/
theorem theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (phi : Ω → ℝ) {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * phi x)) μ)
    (hweight_int : Integrable weight μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * Real.exp (-(k : ℝ) * phi x) ∂μ)
      rate :=
  weightedExactExponentialIntegral_exponentialRateCertificate_of_continuous_min_uniformWeightLower
    μ weight phi hintegrable hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont

/--
Restricted-cell exact-exponential Theorem C.1 certificate for continuous
limiting rates, using an explicit positive-mass condition at the minimizer.
-/
theorem theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_restrict_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phi : Ω → ℝ) {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * phi x))
          (μ.restrict cell))
    (hweight_int : Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U)) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * phi x) ∂μ.restrict cell)
      rate :=
  weightedExactExponentialIntegral_exponentialRateCertificate_of_restrict_continuous_min_uniformWeightLower
    μ hcell weight phi hintegrable hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hlocal_pos

/--
Restricted-cell exact-exponential Theorem C.1 certificate where the minimizer
lies in the closure of the cell interior.  This is the interval-pair cell form
needed by the continuum partition argument.
-/
theorem theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_restrict_closure_interior_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    {cell : Set Ω} (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phi : Ω → ℝ) {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * phi x))
          (μ.restrict cell))
    (hweight_int : Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * phi x) ∂μ.restrict cell)
      rate :=
  weightedExactExponentialIntegral_exponentialRateCertificate_of_restrict_closure_interior_uniformWeightLower
    μ hcell weight phi hintegrable hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hclosure

/--
Weighted Theorem C.1 convenience wrapper for objectives whose weights are
uniformly bounded above and below by positive constants almost everywhere.
-/
theorem theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_uniformWeightLower
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ, Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  weightedLaplaceIntegral_hasExponentialRate_of_uniform_tendsto_essentialInf_uniformWeightLower
    μ weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound hess huniform

/--
Lemma C.3 finite-decomposition algebra: after splitting the piecewise-constant
continuum objective into finitely many interval-pair components, exact
component rate certificates imply that the weighted finite sum has the minimum
component exponent.
-/
theorem lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_min_component
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (componentError : Component → ℕ → ℝ)
    (weight rate : Component → ℝ)
    (hweight_nonneg : ∀ cpt : Component, 0 ≤ weight cpt)
    (hcert :
      ∀ cpt : Component,
        ExponentialRateCertificate (componentError cpt) (rate cpt))
    (minComponent : Component)
    (hweight_pos : 0 < weight minComponent)
    (hrate_ge :
      ∀ cpt : Component, rate minComponent ≤ rate cpt) :
    HasExponentialRate
      (fun k : ℕ => ∑ cpt : Component, weight cpt * componentError cpt k)
      (rate minComponent) :=
  finite_weighted_sum_hasExponentialRate_of_min_component_certificates
    hweight_nonneg hcert minComponent hweight_pos hrate_ge

/--
Lemma C.3 adjacent-dominance algebra: if a selected adjacent subfamily
dominates all interval-pair component rates, then the finite decomposed error
sum decays at the minimum selected adjacent exponent.
-/
theorem lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_dominating_adjacent_subfamily
    {Component Adjacent : Type*} [Fintype Component] [DecidableEq Component]
    (componentError : Component → ℕ → ℝ)
    (weight rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hweight_nonneg : ∀ cpt : Component, 0 ≤ weight cpt)
    (hcert :
      ∀ cpt : Component,
        ExponentialRateCertificate (componentError cpt) (rate cpt))
    (minAdjacent : Adjacent)
    (hweight_pos : 0 < weight (selectAdjacent minAdjacent))
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ cpt : Component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate cpt) :
    HasExponentialRate
      (fun k : ℕ => ∑ cpt : Component, weight cpt * componentError cpt k)
      (rate (selectAdjacent minAdjacent)) :=
  finite_weighted_sum_hasExponentialRate_of_dominating_subfamily_certificates
    selectAdjacent hweight_nonneg hcert minAdjacent hweight_pos
    hadj_min hadj_dominates

/--
Theorem 3.1 adjacent-dominance algebra: with fixed sample weights, shrinking a
success-probability comparison interval weakly lowers the Bernoulli error
exponent. This is the local rate inequality used to reduce wider same-weight
comparisons to adjacent comparisons in the partitioned objective.
-/
theorem theorem31_nested_binary_closed_rate_le
    {gHi gLo pHi pLo pHiAdjacent pLoAdjacent : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_le_adjLo : pLo ≤ pLoAdjacent)
    (hadjLo_le_adjHi : pLoAdjacent ≤ pHiAdjacent)
    (hadjHi_le_pHi : pHiAdjacent ≤ pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHiAdjacent pLoAdjacent ≤
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo :=
  weightedBernoulliClosedThresholdRate_le_of_shrink
    hgHi hgLo hGpos hpLo0 hpLo_le_adjLo hadjLo_le_adjHi
    hadjHi_le_pHi hpHi1

/--
Theorem 3.1 / Lemma C.3 adjacent-dominance step for ordered chains: when the
matching-rate lower bounds and binary levels are monotone, the adjacent
comparison `(i, i+1)` has no larger exponent than any wider comparison
`(i, j)`.
-/
theorem theorem31_monotone_chain_adjacent_rate_le_nonadjacent_rate
    {sampleRate successProb : ℕ → ℝ} {i j : ℕ}
    (hsample_pos : ∀ n, 0 < sampleRate n)
    (hsample_mono : Monotone sampleRate)
    (hprob_mono : Monotone successProb)
    (hprob_i_pos : 0 < successProb i)
    (hprob_j_lt_one : successProb j < 1)
    (hij : i + 1 ≤ j) :
    weightedBernoulliClosedThresholdRate (sampleRate (i + 1)) (sampleRate i)
        (successProb (i + 1)) (successProb i) ≤
      weightedBernoulliClosedThresholdRate (sampleRate j) (sampleRate i)
        (successProb j) (successProb i) :=
  weightedBernoulliClosedThresholdRate_adjacent_le_nonadjacent_of_monotone
    hsample_pos hsample_mono hprob_mono hprob_i_pos hprob_j_lt_one hij

/--
Finite-chain C.3 adjacent-dominance witness for an interior ordered pair:
given any wider comparison `(low, high)`, the adjacent comparison beginning at
`low` has no larger closed Bernoulli exponent. Endpoint comparisons use the
separate endpoint-aware branches, so this theorem exposes the interior case
needed by the closed weighted-rate formula.
-/
theorem theorem31_monotone_finite_chain_adjacent_witness_dominates_ordered_pair
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (low high : Fin (m + 2))
    (hordered : low.val + 1 ≤ high.val)
    (hprob_low_pos : 0 < successProb low)
    (hprob_high_lt_one : successProb high < 1) :
    ∃ adj : Fin (m + 1),
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex adj))
          (sampleRate (adjacentLowIndex adj))
          (successProb (adjacentHighIndex adj))
          (successProb (adjacentLowIndex adj)) ≤
        weightedBernoulliClosedThresholdRate
          (sampleRate high) (sampleRate low)
          (successProb high) (successProb low) := by
  let adj : Fin (m + 1) := ⟨low.val, by omega⟩
  refine ⟨adj, ?_⟩
  have hlow_eq : adjacentLowIndex adj = low := by
    ext
    simp [adj, adjacentLowIndex]
  have hlow_le_adj :
      low.val ≤ (adjacentHighIndex adj).val := by
    simp [adj, adjacentHighIndex]
  have hadj_le_high :
      (adjacentHighIndex adj).val ≤ high.val := by
    simpa [adj, adjacentHighIndex] using hordered
  have hprob_low_le_adj :
      successProb low ≤ successProb (adjacentHighIndex adj) :=
    hprob_mono hlow_le_adj
  have hprob_adj_le_high :
      successProb (adjacentHighIndex adj) ≤ successProb high :=
    hprob_mono hadj_le_high
  have hsample_adj_le_high :
      sampleRate (adjacentHighIndex adj) ≤ sampleRate high :=
    hsample_mono hadj_le_high
  have hprob_adj_pos :
      0 < successProb (adjacentHighIndex adj) :=
    hprob_low_pos.trans_le hprob_low_le_adj
  have hprob_low_lt_one :
      successProb low < 1 :=
    lt_of_le_of_lt (hprob_low_le_adj.trans hprob_adj_le_high)
      hprob_high_lt_one
  have hprob_adj_lt_one :
      successProb (adjacentHighIndex adj) < 1 :=
    lt_of_le_of_lt hprob_adj_le_high hprob_high_lt_one
  have hweight :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex adj)) (sampleRate low)
          (successProb (adjacentHighIndex adj)) (successProb low) ≤
        weightedBernoulliClosedThresholdRate
          (sampleRate high) (sampleRate low)
          (successProb (adjacentHighIndex adj)) (successProb low) :=
    weightedBernoulliClosedThresholdRate_le_of_weights_le
      (hsample_pos (adjacentHighIndex adj)) (hsample_pos low)
      (hsample_pos high) (hsample_pos low)
      hsample_adj_le_high le_rfl
      hprob_adj_pos hprob_adj_lt_one hprob_low_pos hprob_low_lt_one
  have hshrink :
      weightedBernoulliClosedThresholdRate
          (sampleRate high) (sampleRate low)
          (successProb (adjacentHighIndex adj)) (successProb low) ≤
        weightedBernoulliClosedThresholdRate
          (sampleRate high) (sampleRate low)
          (successProb high) (successProb low) :=
    weightedBernoulliClosedThresholdRate_le_of_shrink
      (le_of_lt (hsample_pos high)) (le_of_lt (hsample_pos low))
      (add_pos (hsample_pos high) (hsample_pos low))
      hprob_low_pos le_rfl hprob_low_le_adj hprob_adj_le_high
      hprob_high_lt_one
  simpa [hlow_eq] using hweight.trans hshrink

/--
Low-endpoint C.3 adjacent-dominance step: when the lower level is the source
endpoint `0`, the first adjacent endpoint rate is no larger than the endpoint
rate for any wider comparison starting at that endpoint.
-/
theorem theorem31_first_endpoint_adjacent_rate_le_nonadjacent_endpoint_rate
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_nonneg : ∀ idx, 0 ≤ sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_first_nonneg :
      0 ≤ successProb (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (high : Fin (m + 2))
    (hhigh : 1 ≤ high.val)
    (hprob_high_lt_one : successProb high < 1) :
    sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) *
        (-Real.log
          (1 - successProb
            (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))) ≤
      sampleRate high * (-Real.log (1 - successProb high)) := by
  let firstHigh : Fin (m + 2) :=
    adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))
  have hfirst_val : firstHigh.val = 1 := by
    simp [firstHigh]
  have hfirst_le_high : firstHigh.val ≤ high.val := by
    simpa [hfirst_val] using hhigh
  have hsample_le : sampleRate firstHigh ≤ sampleRate high :=
    hsample_mono hfirst_le_high
  have hprob_le : successProb firstHigh ≤ successProb high :=
    hprob_mono hfirst_le_high
  have hprob_first_lt_one : successProb firstHigh < 1 :=
    lt_of_le_of_lt hprob_le hprob_high_lt_one
  have hfirst_log_nonneg :
      0 ≤ -Real.log (1 - successProb firstHigh) := by
    have hsub_pos : 0 < 1 - successProb firstHigh :=
      sub_pos.mpr hprob_first_lt_one
    have hsub_le_one : 1 - successProb firstHigh ≤ 1 := by
      linarith
    have hlog_le_zero :
        Real.log (1 - successProb firstHigh) ≤ 0 := by
      simpa using Real.log_le_log hsub_pos hsub_le_one
    linarith
  have hlog_mono :
      -Real.log (1 - successProb firstHigh) ≤
        -Real.log (1 - successProb high) := by
    have hsub_high_pos : 0 < 1 - successProb high :=
      sub_pos.mpr hprob_high_lt_one
    have hsub_le : 1 - successProb high ≤ 1 - successProb firstHigh := by
      linarith
    have hlog_le :
        Real.log (1 - successProb high) ≤
          Real.log (1 - successProb firstHigh) :=
      Real.log_le_log hsub_high_pos hsub_le
    linarith
  have hsample_high_nonneg : 0 ≤ sampleRate high :=
    hsample_nonneg high
  calc
    sampleRate firstHigh * (-Real.log (1 - successProb firstHigh))
        ≤ sampleRate high * (-Real.log (1 - successProb firstHigh)) := by
          exact mul_le_mul_of_nonneg_right hsample_le hfirst_log_nonneg
    _ ≤ sampleRate high * (-Real.log (1 - successProb high)) := by
          exact mul_le_mul_of_nonneg_left hlog_mono hsample_high_nonneg

/--
Top-endpoint C.3 adjacent-dominance witness: when a wider comparison ends at
the source endpoint `1`, either it is already the last adjacent endpoint
comparison or the interior adjacent comparison starting at `low` has no larger
closed Bernoulli exponent than the endpoint exponent
`sampleRate low * (-log (successProb low))`.
-/
theorem theorem31_top_endpoint_adjacent_witness_dominates_nonadjacent_endpoint_rate
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_not_last_lt_one :
      ∀ idx : Fin (m + 2), idx.val < m + 1 → successProb idx < 1)
    (low : Fin (m + 2))
    (hlow_pos : 0 < low.val)
    (hlow_le_last_adjacent : low.val ≤ m)
    (hprob_low_pos : 0 < successProb low) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        sampleRate low * (-Real.log (successProb low)) := by
  by_cases hlast : low.val = m
  · let adj : Fin (m + 1) := lastAdjacentIndex
    refine ⟨adj, ?_⟩
    have hlow_eq : adjacentLowIndex adj = low := by
      ext
      simp [adj, lastAdjacentIndex, adjacentLowIndex, hlast]
    have hm_pos : 0 < m := by
      omega
    have hadj_not_first : adj.val ≠ 0 := by
      simpa [adj] using ne_of_gt hm_pos
    have hrate_eq :
        binaryEndpointAwareAdjacentRate successProb sampleRate adj =
          sampleRate low * (-Real.log (successProb low)) := by
      simp [binaryEndpointAwareAdjacentRate, adj, lastAdjacentIndex,
        hadj_not_first, hlow_eq]
    rw [hrate_eq]
  · have hlow_lt_m : low.val < m := by
      omega
    let adj : Fin (m + 1) := ⟨low.val, by omega⟩
    refine ⟨adj, ?_⟩
    have hlow_eq : adjacentLowIndex adj = low := by
      ext
      simp [adj, adjacentLowIndex]
    have hlow_le_high :
        low.val ≤ (adjacentHighIndex adj).val := by
      simp [adj, adjacentHighIndex]
    have hprob_low_le_high :
        successProb low ≤ successProb (adjacentHighIndex adj) :=
      hprob_mono hlow_le_high
    have hprob_high_pos :
        0 < successProb (adjacentHighIndex adj) :=
      hprob_low_pos.trans_le hprob_low_le_high
    have hprob_high_lt_one :
        successProb (adjacentHighIndex adj) < 1 := by
      refine hprob_not_last_lt_one (adjacentHighIndex adj) ?_
      simp [adj, adjacentHighIndex]
      omega
    have hprob_low_lt_one : successProb low < 1 :=
      lt_of_le_of_lt hprob_low_le_high hprob_high_lt_one
    have hadj_not_first : adj.val ≠ 0 := by
      simpa [adj] using ne_of_gt hlow_pos
    have hadj_not_last : adj.val ≠ m := by
      simp [adj]
      omega
    have hrate_eq :
        binaryEndpointAwareAdjacentRate successProb sampleRate adj =
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex adj))
            (sampleRate low)
            (successProb (adjacentHighIndex adj))
            (successProb low) := by
      simp [binaryEndpointAwareAdjacentRate, hadj_not_first, hadj_not_last,
        hlow_eq]
    have hclosed_le :
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex adj))
            (sampleRate low)
            (successProb (adjacentHighIndex adj))
            (successProb low) ≤
          sampleRate low * (-Real.log (successProb low)) :=
      weightedBernoulliClosedThresholdRate_le_low_success_endpoint
        (hsample_pos (adjacentHighIndex adj)) (hsample_pos low)
        hprob_high_pos hprob_high_lt_one
        hprob_low_pos hprob_low_lt_one hprob_low_le_high
    simpa [hrate_eq] using hclosed_le

/--
Theorem 3.1 / Lemma C.3 endpoint-aware adjacent-dominance package for finite
real-rate components. Every wider ordered pair except the pure
bottom-to-top source-endpoint pair is dominated by an adjacent comparison under
the paper's endpoint-aware rate convention.
-/
theorem theorem31_endpoint_aware_adjacent_witness_dominates_ordered_pair
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (low high : Fin (m + 2))
    (hordered : low.val + 1 ≤ high.val)
    (hnot_bottom_to_top : low.val ≠ 0 ∨ high.val ≠ m + 1) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        binaryEndpointAwarePairRate successProb sampleRate low high := by
  by_cases hlow_first : low.val = 0
  · have hhigh_not_last : high.val ≠ m + 1 := by
      rcases hnot_bottom_to_top with hlow_ne | hhigh_ne
      · exact False.elim (hlow_ne hlow_first)
      · exact hhigh_ne
    have hhigh_ge_one : 1 ≤ high.val := by
      omega
    let adj : Fin (m + 1) := firstAdjacentIndex
    refine ⟨adj, ?_⟩
    have hsample_nonneg : ∀ idx, 0 ≤ sampleRate idx :=
      fun idx => (hsample_pos idx).le
    have hfirst :
        sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) *
            (-Real.log
              (1 - successProb
                (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))) ≤
          sampleRate high * (-Real.log (1 - successProb high)) :=
      theorem31_first_endpoint_adjacent_rate_le_nonadjacent_endpoint_rate
        sampleRate successProb hsample_nonneg hsample_mono hprob_mono
        (hprob_nonneg
          (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
        high hhigh_ge_one (hprob_lt_one_of_not_last high hhigh_not_last)
    have hadj_eq :
        binaryEndpointAwareAdjacentRate successProb sampleRate adj =
          sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) *
            (-Real.log
              (1 - successProb
                (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))) := by
      simp [binaryEndpointAwareAdjacentRate, adj, firstAdjacentIndex]
    have hpair_eq :
        binaryEndpointAwarePairRate successProb sampleRate low high =
          sampleRate high * (-Real.log (1 - successProb high)) := by
      simp [binaryEndpointAwarePairRate, hlow_first]
    simpa [hadj_eq, hpair_eq] using hfirst
  · by_cases hhigh_last : high.val = m + 1
    · have hlow_pos_nat : 0 < low.val := Nat.pos_of_ne_zero hlow_first
      have hlow_le_last_adjacent : low.val ≤ m := by
        omega
      have htop :=
        theorem31_top_endpoint_adjacent_witness_dominates_nonadjacent_endpoint_rate
          sampleRate successProb hsample_pos hprob_mono
          (fun idx hlt =>
            hprob_lt_one_of_not_last idx (by omega))
          low hlow_pos_nat hlow_le_last_adjacent
          (hprob_pos_of_not_first low hlow_first)
      rcases htop with ⟨adj, hadj⟩
      refine ⟨adj, ?_⟩
      have hpair_eq :
          binaryEndpointAwarePairRate successProb sampleRate low high =
            sampleRate low * (-Real.log (successProb low)) := by
        simp [binaryEndpointAwarePairRate, hlow_first, hhigh_last]
      simpa [hpair_eq] using hadj
    · have hlow_lt_m : low.val < m := by
        omega
      let adj : Fin (m + 1) := ⟨low.val, by omega⟩
      refine ⟨adj, ?_⟩
      have hlow_eq : adjacentLowIndex adj = low := by
        ext
        simp [adj, adjacentLowIndex]
      have hlow_le_adj :
          low.val ≤ (adjacentHighIndex adj).val := by
        simp [adj, adjacentHighIndex]
      have hadj_le_high :
          (adjacentHighIndex adj).val ≤ high.val := by
        simpa [adj, adjacentHighIndex] using hordered
      have hprob_low_pos : 0 < successProb low :=
        hprob_pos_of_not_first low hlow_first
      have hprob_high_lt_one : successProb high < 1 :=
        hprob_lt_one_of_not_last high hhigh_last
      have hprob_low_le_adj :
          successProb low ≤ successProb (adjacentHighIndex adj) :=
        hprob_mono hlow_le_adj
      have hprob_adj_le_high :
          successProb (adjacentHighIndex adj) ≤ successProb high :=
        hprob_mono hadj_le_high
      have hsample_adj_le_high :
          sampleRate (adjacentHighIndex adj) ≤ sampleRate high :=
        hsample_mono hadj_le_high
      have hprob_adj_pos :
          0 < successProb (adjacentHighIndex adj) :=
        hprob_low_pos.trans_le hprob_low_le_adj
      have hprob_low_lt_one :
          successProb low < 1 :=
        lt_of_le_of_lt (hprob_low_le_adj.trans hprob_adj_le_high)
          hprob_high_lt_one
      have hprob_adj_lt_one :
          successProb (adjacentHighIndex adj) < 1 :=
        lt_of_le_of_lt hprob_adj_le_high hprob_high_lt_one
      have hweight :
          weightedBernoulliClosedThresholdRate
              (sampleRate (adjacentHighIndex adj)) (sampleRate low)
              (successProb (adjacentHighIndex adj)) (successProb low) ≤
            weightedBernoulliClosedThresholdRate
              (sampleRate high) (sampleRate low)
              (successProb (adjacentHighIndex adj)) (successProb low) :=
        weightedBernoulliClosedThresholdRate_le_of_weights_le
          (hsample_pos (adjacentHighIndex adj)) (hsample_pos low)
          (hsample_pos high) (hsample_pos low)
          hsample_adj_le_high le_rfl
          hprob_adj_pos hprob_adj_lt_one hprob_low_pos hprob_low_lt_one
      have hshrink :
          weightedBernoulliClosedThresholdRate
              (sampleRate high) (sampleRate low)
              (successProb (adjacentHighIndex adj)) (successProb low) ≤
            weightedBernoulliClosedThresholdRate
              (sampleRate high) (sampleRate low)
              (successProb high) (successProb low) :=
        weightedBernoulliClosedThresholdRate_le_of_shrink
          (le_of_lt (hsample_pos high)) (le_of_lt (hsample_pos low))
          (add_pos (hsample_pos high) (hsample_pos low))
          hprob_low_pos le_rfl hprob_low_le_adj hprob_adj_le_high
          hprob_high_lt_one
      have hadj_not_first : adj.val ≠ 0 := by
        simpa [adj] using hlow_first
      have hadj_not_last : adj.val ≠ m := by
        simp [adj]
        omega
      have hadj_rate_eq :
          binaryEndpointAwareAdjacentRate successProb sampleRate adj =
            weightedBernoulliClosedThresholdRate
              (sampleRate (adjacentHighIndex adj))
              (sampleRate low)
              (successProb (adjacentHighIndex adj))
              (successProb low) := by
        simp [binaryEndpointAwareAdjacentRate, hadj_not_first, hadj_not_last,
          hlow_eq]
      have hpair_rate_eq :
          binaryEndpointAwarePairRate successProb sampleRate low high =
            weightedBernoulliClosedThresholdRate
              (sampleRate high) (sampleRate low)
              (successProb high) (successProb low) := by
        simp [binaryEndpointAwarePairRate, hlow_first, hhigh_last]
      simpa [hadj_rate_eq, hpair_rate_eq] using hweight.trans hshrink

/--
Selected-pair form of the endpoint-aware adjacent-dominance package.  This is
the exact finite dominance fact needed by the ordered-rectangle C.3 bridge.
-/
theorem theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (component :
      {piece : Fin (m + 2) × Fin (m + 2) //
        theorem31OrderedNontrivialPairSelected (m := m) piece}) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        binaryEndpointAwarePairRate successProb sampleRate
          component.val.1 component.val.2 := by
  rcases component with ⟨⟨low, high⟩, hselected⟩
  exact
    theorem31_endpoint_aware_adjacent_witness_dominates_ordered_pair
      sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
      hprob_pos_of_not_first hprob_lt_one_of_not_last low high
      hselected.1 hselected.2

/--
Selected-pair adjacent-dominance package with the endpoint support and
success-probability monotonicity supplied by `BinaryEndpointLevelVector`.
-/
theorem theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair_of_endpointLevelVector
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (component : theorem31OrderedNontrivialPairComponent m) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        binaryEndpointAwarePairRate successProb sampleRate
          component.val.1 component.val.2 :=
  theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
    sampleRate successProb hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    component

/--
Selected ordered-pair positivity for the paper's floor-count pairwise error
kernel.  The selected-pair predicate excludes only the pure bottom-to-top
endpoint pair: if the high endpoint is not top, all-failure samples give a tie;
otherwise the low endpoint is not bottom, and all-success samples eventually
give a tie once both floor counts are positive.
-/
theorem binaryRatingModel_floorPkComplementErrorProb_eventually_pos_of_selected_ordered_pair
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (component : theorem31OrderedNontrivialPairComponent m) :
    ∀ᶠ k : ℕ in Filter.atTop,
      0 <
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          component.val.2 component.val.1 k := by
  rcases component with ⟨⟨low, high⟩, hselected⟩
  by_cases hhigh_last : high.val = m + 1
  · have hlow_not_first : low.val ≠ 0 := by
      rcases hselected.2 with hlow_ne | hhigh_ne
      · exact hlow_ne
      · exact False.elim (hhigh_ne hhigh_last)
    have hhigh_not_first : high.val ≠ 0 := by
      have hordered : low.val + 1 ≤ high.val := hselected.1
      omega
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_floorPkComplementErrorProb_eventually_pos_of_pos
        successProb hprob0 hprob1 sampleRate high low
        (hsample_pos high) (hsample_pos low)
        (hprob_pos_of_not_first high hhigh_not_first)
        (hprob_pos_of_not_first low hlow_not_first)
  · have hlow_not_last : low.val ≠ m + 1 := by
      have hordered : low.val + 1 ≤ high.val := hselected.1
      have hhigh_lt : high.val < m + 2 := high.isLt
      omega
    have hpHi_lt_one : successProb high < 1 :=
      hprob_lt_one_of_not_last high hhigh_last
    have hpLo_lt_one : successProb low < 1 :=
      hprob_lt_one_of_not_last low hlow_not_last
    filter_upwards with k
    simpa [binaryRatingModel] using
      realBinaryRatingLDPModel_floorPkComplementErrorProb_pos_of_lt_one
        successProb hprob0 hprob1 sampleRate high low k
        hpHi_lt_one hpLo_lt_one

/--
Selected ordered-pair left-tail certificate for the endpoint-aware rate
convention. This extends the adjacent-pair certificate split to any selected
nontrivial ordered pair used by the C.3 rectangle decomposition.
-/
theorem binaryEndpointAwarePairRate_leftTail_certificate_of_selected_ordered_pair
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : theorem31OrderedNontrivialPairComponent m) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate
        component.val.2 component.val.1)
      (binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2) := by
  rcases component with ⟨⟨low, high⟩, hselected⟩
  by_cases hlow_first : low.val = 0
  · have hhigh_not_last : high.val ≠ m + 1 := by
      rcases hselected.2 with hlow_ne | hhigh_ne
      · exact False.elim (hlow_ne hlow_first)
      · exact hhigh_ne
    have hhigh_not_first : high.val ≠ 0 := by
      have hordered : low.val + 1 ≤ high.val := hselected.1
      omega
    have hpLo_zero : successProb low = 0 := by
      have hfirst_level :
          low = (firstLevelIndex : Fin (m + 2)) := by
        ext
        simpa [firstLevelIndex] using hlow_first
      simpa [hfirst_level] using hfirst_zero
    have hcert :=
      binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_low_success_zero
        successProb hprob0 hprob1 sampleRate high low
        (hsample_pos high)
        (hprob_pos_of_not_first high hhigh_not_first)
        (hprob_lt_one_of_not_last high hhigh_not_last)
        hpLo_zero
    simpa [binaryEndpointAwarePairRate, hlow_first] using hcert
  · by_cases hhigh_last : high.val = m + 1
    · have hlow_not_last : low.val ≠ m + 1 := by
        have hordered : low.val + 1 ≤ high.val := hselected.1
        have hhigh_lt : high.val < m + 2 := high.isLt
        omega
      have hpHi_one : successProb high = 1 := by
        have hlast_level :
            high = (lastLevelIndex : Fin (m + 2)) := by
          ext
          simpa [lastLevelIndex] using hhigh_last
        simpa [hlast_level] using hlast_one
      have hcert :=
        binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_high_success_one
          successProb hprob0 hprob1 sampleRate high low
          (hsample_pos high) (hsample_pos low)
          hpHi_one
          (hprob_pos_of_not_first low hlow_first)
          (hprob_lt_one_of_not_last low hlow_not_last)
      simpa [binaryEndpointAwarePairRate, hlow_first, hhigh_last] using hcert
    · have hlow_not_last : low.val ≠ m + 1 := by
        have hordered : low.val + 1 ≤ high.val := hselected.1
        have hhigh_lt : high.val < m + 2 := high.isLt
        omega
      have hlow_le_high : low.val ≤ high.val := by
        have hordered : low.val + 1 ≤ high.val := hselected.1
        omega
      have hhigh_not_first : high.val ≠ 0 := by
        have hordered : low.val + 1 ≤ high.val := hselected.1
        omega
      have hpLo_le_hi : successProb low ≤ successProb high :=
        hprob_mono hlow_le_high
      have hcert :=
        binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
          successProb hprob0 hprob1 sampleRate high low
          (hsample_pos high) (hsample_pos low)
          (hprob_pos_of_not_first high hhigh_not_first)
          (hprob_lt_one_of_not_last high hhigh_last)
          (hprob_pos_of_not_first low hlow_first)
          (hprob_lt_one_of_not_last low hlow_not_last)
          hpLo_le_hi
      simpa [binaryEndpointAwarePairRate, hlow_first, hhigh_last] using hcert

/--
Selected ordered-pair `1 - P_k` certificate for the endpoint-aware rate
convention.
-/
theorem binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : theorem31OrderedNontrivialPairComponent m) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate
        component.val.2 component.val.1)
      (binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2) :=
  twoSampleFloorPkComplementError_exponentialRateCertificate_of_leftTail
    (binaryRatingModel successProb hprob0 hprob1) sampleRate
    component.val.2 component.val.1
    (binaryEndpointAwarePairRate_leftTail_certificate_of_selected_ordered_pair
      successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hprob_mono
      hprob_pos_of_not_first hprob_lt_one_of_not_last hsample_pos component)

/--
Selected ordered-pair `1 - P_k` certificate with endpoint values, support, and
monotonicity supplied by `BinaryEndpointLevelVector`.
-/
theorem binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair_of_endpointLevelVector
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : theorem31OrderedNontrivialPairComponent m) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb
          (BinaryEndpointLevelVector_nonneg hlevels)
          (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
        component.val.2 component.val.1)
      (binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2) :=
  binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair
    successProb sampleRate
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_le_one hlevels)
    hlevels.1 hlevels.2.1
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    hsample_pos component

/--
Finite Lemma C.3 selected ordered-pair aggregation with the component
certificates discharged by the endpoint-aware binary model.  This is the
finite endpoint-pair version of the C.3 adjacent-dominance reduction: the
weighted sum of all selected ordered-pair endpoint errors has the minimum
adjacent endpoint-aware exponent.
-/
theorem lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    {weight : theorem31OrderedNontrivialPairComponent m → ℝ}
    (hweight_nonneg :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 ≤ weight component)
    (minAdjacent : Fin (m + 1))
    (hweight_pos :
      0 < weight (theorem31OrderedAdjacentPiece hm minAdjacent))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∑ component : theorem31OrderedNontrivialPairComponent m,
          weight component *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              component.val.2 component.val.1 k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let componentError : theorem31OrderedNontrivialPairComponent m → ℕ → ℝ :=
    fun component k =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate
        component.val.2 component.val.1 k
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) → theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hcert :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ExponentialRateCertificate
          (componentError component) (rate component) := by
    intro component
    exact
      binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair
        successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hprob_mono
        hprob_pos_of_not_first hprob_lt_one_of_not_last hsample_pos component
  have hsub_min :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hdominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1), rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob0
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hsum :=
    lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_dominating_adjacent_subfamily
      (componentError := componentError) (weight := weight) (rate := rate)
      (selectAdjacent := selectAdjacent) hweight_nonneg hcert minAdjacent
      hweight_pos hsub_min hdominates
  simpa [componentError, rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hsum

/--
Finite Lemma C.3 selected ordered-pair aggregation with the paper's endpoint
level-vector convention discharging the finite binary-model side conditions.
-/
theorem lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min_of_endpointLevelVector
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    {weight : theorem31OrderedNontrivialPairComponent m → ℝ}
    (hweight_nonneg :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 ≤ weight component)
    (minAdjacent : Fin (m + 1))
    (hweight_pos :
      0 < weight (theorem31OrderedAdjacentPiece hm minAdjacent))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∑ component : theorem31OrderedNontrivialPairComponent m,
          weight component *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb
                (BinaryEndpointLevelVector_nonneg hlevels)
                (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
              component.val.2 component.val.1 k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min
    hm successProb sampleRate
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_le_one hlevels)
    hlevels.1 hlevels.2.1 hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    hweight_nonneg minAdjacent hweight_pos hadj_min

/--
Selected ordered-pair constant-kernel normalized-log certificate for the C.3
Laplace bridge. The endpoint-pair kernel is independent of the continuum
rectangle parameter, so the scalar exact-rate certificate is uniform on every
parameter set.
-/
theorem binaryEndpointAwarePairRate_floorPkComplementError_uniform_constant_kernel_certificate_of_selected_ordered_pair
    {α : Type*} {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : theorem31OrderedNontrivialPairComponent m)
    (s : Set α) :
    UniformNormalizedLogRateCertificateOn
      (fun k (_x : α) =>
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          component.val.2 component.val.1 k)
      (fun _x : α =>
        binaryEndpointAwarePairRate successProb sampleRate
          component.val.1 component.val.2)
      s :=
  UniformNormalizedLogRateCertificateOn.of_constant_exponentialRateCertificate
    (binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair
      successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hprob_mono
      hprob_pos_of_not_first hprob_lt_one_of_not_last hsample_pos component)

/--
Selected ordered-pair constant-kernel normalized-log certificate with the
endpoint support and monotonicity facts supplied by `BinaryEndpointLevelVector`.
-/
theorem binaryEndpointAwarePairRate_floorPkComplementError_uniform_constant_kernel_certificate_of_selected_ordered_pair_of_endpointLevelVector
    {α : Type*} {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : theorem31OrderedNontrivialPairComponent m)
    (s : Set α) :
    UniformNormalizedLogRateCertificateOn
      (fun k (_x : α) =>
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb
            (BinaryEndpointLevelVector_nonneg hlevels)
            (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
          component.val.2 component.val.1 k)
      (fun _x : α =>
        binaryEndpointAwarePairRate successProb sampleRate
          component.val.1 component.val.2)
      s :=
  UniformNormalizedLogRateCertificateOn.of_constant_exponentialRateCertificate
    (binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair_of_endpointLevelVector
      successProb sampleRate hlevels hsample_pos component)

/--
Lemma C.3 measurable-partition decomposition: once the continuum
piecewise-constant objective has been split into a finite measurable partition
and every component integral has an exact rate certificate, the whole support
integral has the minimum component exponent.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_min_component_certificates
    {Ω Component : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω)
    (P : FiniteMeasurableSetPartition μ Component)
    (errorKernel : ℕ → Ω → ℝ)
    (rate : Component → ℝ)
    (hcomponent_int :
      ∀ k component, IntegrableOn (errorKernel k) (P.pieceSet component) μ)
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ => P.componentIntegral (errorKernel k) component)
          (rate component))
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ => ∫ x in P.support, errorKernel k x ∂μ)
      (rate minComponent) :=
  P.setIntegral_hasExponentialRate_of_min_component_certificates
    errorKernel rate hcomponent_int hcert minComponent hrate_ge

/--
Lemma C.3 measurable-partition adjacent-dominance bridge: a selected adjacent
subfamily that dominates all component rates determines the exponent of the
whole partitioned continuum objective.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily
    {Ω Component Adjacent : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω)
    (P : FiniteMeasurableSetPartition μ Component)
    (errorKernel : ℕ → Ω → ℝ)
    (rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hcomponent_int :
      ∀ k component, IntegrableOn (errorKernel k) (P.pieceSet component) μ)
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ => P.componentIntegral (errorKernel k) component)
          (rate component))
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ => ∫ x in P.support, errorKernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  P.setIntegral_hasExponentialRate_of_dominating_subfamily_certificates
    errorKernel rate selectAdjacent hcomponent_int hcert minAdjacent
    hadj_min hadj_dominates

/--
Lemma C.3 measurable-partition positive-kernel bridge: if every component
kernel has a uniform normalized-log rate limit, the partitioned weighted
continuum error integral decays at the minimum component exponent.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate
    {Ω Component : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (hess :
      ∀ component,
        HasAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) (phi component) (rate component))
    (hweighted_near :
      ∀ component,
        HasPositiveWeightNearAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) weight (phi component) (rate component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate minComponent) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_min_component_uniform_logRate
    weight kernel phi rate W hkernel_int hweight_int hWpos
    hweight_nonneg hweight_bound hess hweighted_near hkernel_pos
    huniform_log minComponent hrate_ge

/--
Lemma C.3 measurable-partition positive-kernel adjacent-dominance bridge:
componentwise uniform normalized-log rate limits plus adjacent dominance
determine the exponent of the partitioned continuum error integral.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_uniform_logRate
    {Ω Component Adjacent : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (hess :
      ∀ component,
        HasAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) (phi component) (rate component))
    (hweighted_near :
      ∀ component,
        HasPositiveWeightNearAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) weight (phi component) (rate component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_uniform_logRate
    weight kernel phi rate W selectAdjacent hkernel_int hweight_int hWpos
    hweight_nonneg hweight_bound hess hweighted_near hkernel_pos
    huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 measurable-partition bridge with source-style continuous minimizers:
uniform componentwise log-rate convergence, a continuous local minimizer in
each cell, local positive cell mass, and uniformly positive weights imply that
the partitioned weighted continuum error integral decays at the minimum
component exponent.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_min_component_continuous_min_uniformWeightLower
    {Ω Component : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlocal_pos :
      ∀ component U, IsOpen U → x0 component ∈ U →
        0 < μ (P.pieceSet component ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate minComponent) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_min_component_restrict_continuous_min_uniformWeightLower
    weight kernel phi rate W c hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hlocal_pos hkernel_pos
    huniform_log minComponent hrate_ge

/--
Lemma C.3 adjacent-dominance bridge with source-style continuous minimizers:
the previous continuous-minimizer partition bridge plus adjacent dominance
determines the exponent of the full partitioned continuum objective from the
minimum selected adjacent component.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_uniformWeightLower
    {Ω Component Adjacent : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlocal_pos :
      ∀ component U, IsOpen U → x0 component ∈ U →
        0 < μ (P.pieceSet component ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_continuous_min_uniformWeightLower
    weight kernel phi rate W c selectAdjacent hkernel_int hweight_int hWpos
    hcpos hweight_lower hweight_bound x0 hmin hx0 hcont hlocal_pos
    hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 measurable-partition bridge with source-style continuous minimizers
and topological cell support: if each component minimizer lies in the closure of
that component's interior under an open-positive ambient measure, the local
positive-mass condition required by the Laplace step follows automatically.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_min_component_closure_interior_uniformWeightLower
    {Ω Component : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate minComponent) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_min_component_restrict_closure_interior_uniformWeightLower
    weight kernel phi rate W c hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hclosure hkernel_pos
    huniform_log minComponent hrate_ge

/--
Lemma C.3 adjacent-dominance bridge with closure/interior cell support.  This is
the source-shaped finite partition rate theorem after the local positive-mass
Laplace condition has been discharged topologically.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_uniformWeightLower
    {Ω Component Adjacent : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_uniformWeightLower
    weight kernel phi rate W c selectAdjacent hkernel_int hweight_int hWpos
    hcpos hweight_lower hweight_bound x0 hmin hx0 hcont hclosure
    hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 adjacent-dominance bridge with closure/interior support and global
constant weight bounds.  This packages the common case where the same positive
lower and upper constants work on every partition cell.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_uniformWeightLower_constBounds
    {Ω Component Adjacent : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component) {W c : ℝ}
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_uniformWeightLower_constBounds
    weight kernel phi rate selectAdjacent hkernel_int hweight_int
    hWpos hcpos hweight_lower hweight_bound x0 hmin hx0 hcont
    hclosure hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 measurable-partition bridge with closure/interior cell support and
locally positive objective weights.  This is the source-shaped version for
continuous positive weights when no uniform lower-bound constant is supplied.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_min_component_closure_interior_weight_pos
    {Ω Component : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hphi_cont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate minComponent) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_min_component_restrict_closure_interior_weight_pos
    weight kernel phi rate W hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hclosure hkernel_pos huniform_log minComponent hrate_ge

/--
Lemma C.3 adjacent-dominance bridge with closure/interior cell support and
locally positive objective weights.
-/
theorem lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_weight_pos
    {Ω Component Adjacent : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hkernel_int :
      ∀ k component,
        IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hphi_cont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  P.setIntegral_weightedKernel_hasExponentialRate_of_dominating_subfamily_restrict_closure_interior_weight_pos
    weight kernel phi rate W selectAdjacent hkernel_int hweight_int hWpos
    hweight_nonneg hweight_bound x0 hmin hx0 hphi_cont hweight_cont
    hweight_x0_pos hclosure hkernel_pos huniform_log minAdjacent hadj_min
    hadj_dominates

/--
Theorem 3.1/C.3 ordered quality partition: monotone cutpoints split the
continuum quality interval into the half-open cells used by a stepwise binary
rating rule.
-/
def theorem31_ordered_quality_interval_partition
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut) :
    FiniteMeasurableSetPartition μ (Fin n) :=
  FiniteMeasurableSetPartition.orderedRealIocNatCutpoints μ n cut hmono

/--
Theorem 3.1/C.3 ordered quality-pair partition: selected products of ordered
quality cells give the finite rectangle family used to decompose the pairwise
continuum error integral.
-/
def theorem31_ordered_quality_pair_partition
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected] :
    FiniteMeasurableSetPartition (μ.prod μ)
      {piece : Fin n × Fin n // selected piece} :=
  (theorem31_ordered_quality_interval_partition μ n cut hmono).selectedProduct
    (theorem31_ordered_quality_interval_partition μ n cut hmono) selected

/--
Canonical interior point of a selected ordered pair cell, obtained by taking
the midpoint of each coordinate interval.
-/
def theorem31_ordered_quality_pair_component_midpoint {m : ℕ}
    (cut : ℕ → ℝ) (component : theorem31OrderedNontrivialPairComponent m) :
    ℝ × ℝ :=
  FiniteMeasurableSetPartition.orderedRealIocNatCutpointsProdMidpoint
    cut cut component.val

/--
If adjacent cutpoints are strictly increasing, the canonical midpoint lies in
the selected ordered pair cell.
-/
theorem theorem31_ordered_quality_pair_component_midpoint_mem
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (component : theorem31OrderedNontrivialPairComponent m) :
    theorem31_ordered_quality_pair_component_midpoint cut component ∈
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet
          component := by
  exact
    FiniteMeasurableSetPartition.selectedProduct_orderedRealIocNatCutpoints_midpoint_mem
      μ μ (m + 2) (m + 2) cut cut hmono hmono
      (theorem31OrderedNontrivialPairSelected (m := m)) component
      (hcut_strict component.val.1.val component.val.1.isLt)
      (hcut_strict component.val.2.val component.val.2.isLt)

/--
Theorem 3.1/C.3 ordered interval support: every point of an ordered
half-open quality cell lies in the closure of that cell's interior.
-/
theorem theorem31_ordered_quality_interval_piece_mem_closure_interior
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (piece : Fin n) {x : ℝ}
    (hx :
      x ∈ (theorem31_ordered_quality_interval_partition μ n cut hmono).pieceSet
        piece) :
    x ∈ closure
      (interior
        ((theorem31_ordered_quality_interval_partition μ n cut hmono).pieceSet
          piece)) :=
  FiniteMeasurableSetPartition.orderedRealIocNatCutpoints_piece_mem_closure_interior
    μ n cut hmono piece hx

/--
Theorem 3.1/C.3 ordered rectangle support: every point of a selected ordered
quality-pair rectangle lies in the closure of that rectangle's interior.
-/
theorem theorem31_ordered_quality_pair_piece_mem_closure_interior
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (piece : {piece : Fin n × Fin n // selected piece}) {x : ℝ × ℝ}
    (hx :
      x ∈ (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
        piece) :
    x ∈ closure
      (interior
        ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          piece)) :=
  FiniteMeasurableSetPartition.selectedProduct_piece_mem_closure_interior
    (theorem31_ordered_quality_interval_partition μ n cut hmono)
    (theorem31_ordered_quality_interval_partition μ n cut hmono)
    (fun piece x hx =>
      theorem31_ordered_quality_interval_piece_mem_closure_interior
        μ n cut hmono piece hx)
    (fun piece x hx =>
      theorem31_ordered_quality_interval_piece_mem_closure_interior
        μ n cut hmono piece hx)
    selected piece hx

/--
Theorem 3.1/C.3 closed-rectangle compact superset for a selected ordered
quality-pair cell.
-/
def theorem31_ordered_quality_pair_compactSuperset
    (n : ℕ) (cut : ℕ → ℝ)
    (piece : Fin n × Fin n) : Set (ℝ × ℝ) :=
  FiniteMeasurableSetPartition.orderedRealIocNatCutpointsProdCompactSuperset
    n n cut cut piece

/--
Theorem 3.1/C.3 compactness of the closed-rectangle superset for a selected
ordered quality-pair cell.
-/
theorem theorem31_ordered_quality_pair_compactSuperset_isCompact
    (n : ℕ) (cut : ℕ → ℝ)
    (piece : Fin n × Fin n) :
    IsCompact (theorem31_ordered_quality_pair_compactSuperset n cut piece) :=
  FiniteMeasurableSetPartition.orderedRealIocNatCutpointsProdCompactSuperset_isCompact
    n n cut cut piece

/--
Theorem 3.1/C.3 selected ordered quality-pair cells are contained in their
closed-rectangle compact supersets.
-/
theorem theorem31_ordered_quality_pair_piece_subset_compactSuperset
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (piece : {piece : Fin n × Fin n // selected piece}) :
    (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
      piece ⊆
        theorem31_ordered_quality_pair_compactSuperset n cut piece.val :=
  FiniteMeasurableSetPartition.selectedProduct_orderedRealIocNatCutpoints_piece_subset_prodCompactSuperset
    μ μ n n cut cut hmono hmono selected piece

/--
Closed-cell coordinate order for the source's low-high selected-pair
convention: if the first interval index lies below the second, then all points
in the compact cell superset satisfy `q.1 ≤ q.2`.
-/
theorem theorem31_ordered_quality_pair_compactSuperset_fst_le_snd_of_index_fst_succ_le_snd
    {n : ℕ} {cut : ℕ → ℝ} (hmono : Monotone cut)
    {piece : Fin n × Fin n}
    (hindex : piece.1.val + 1 ≤ piece.2.val) :
    ∀ q : ℝ × ℝ,
      q ∈ theorem31_ordered_quality_pair_compactSuperset n cut piece →
        q.1 ≤ q.2 := by
  simpa [theorem31_ordered_quality_pair_compactSuperset] using
    FiniteMeasurableSetPartition.orderedRealIocNatCutpointsProdCompactSuperset_fst_le_snd_of_index_fst_succ_le_snd
      n n cut hmono piece hindex

/--
Closed-cell coordinate order for the reverse high-low selected-pair
convention: if the second interval index lies below the first, then all points
in the compact cell superset satisfy `q.2 ≤ q.1`.
-/
theorem theorem31_ordered_quality_pair_compactSuperset_snd_le_fst_of_index_snd_succ_le_fst
    {n : ℕ} {cut : ℕ → ℝ} (hmono : Monotone cut)
    {piece : Fin n × Fin n}
    (hindex : piece.2.val + 1 ≤ piece.1.val) :
    ∀ q : ℝ × ℝ,
      q ∈ theorem31_ordered_quality_pair_compactSuperset n cut piece →
        q.2 ≤ q.1 := by
  simpa [theorem31_ordered_quality_pair_compactSuperset] using
    FiniteMeasurableSetPartition.orderedRealIocNatCutpointsProdCompactSuperset_snd_le_fst_of_index_snd_succ_le_fst
      n n cut hmono piece hindex

/--
On a low-high closed selected cell, monotonicity of the success-probability
curve implies the corresponding probability order.
-/
theorem theorem31_ordered_quality_pair_compactSuperset_successProb_fst_le_snd_of_mono_of_index_fst_succ_le_snd
    {n : ℕ} {cut : ℕ → ℝ} (hmono : Monotone cut)
    {piece : Fin n × Fin n}
    (hindex : piece.1.val + 1 ≤ piece.2.val)
    {successProb : ℝ → ℝ} (hprob_mono : Monotone successProb) :
    ∀ q : ℝ × ℝ,
      q ∈ theorem31_ordered_quality_pair_compactSuperset n cut piece →
        successProb q.1 ≤ successProb q.2 := by
  intro q hq
  exact hprob_mono
    (theorem31_ordered_quality_pair_compactSuperset_fst_le_snd_of_index_fst_succ_le_snd
      hmono hindex q hq)

/--
On a high-low closed selected cell, monotonicity of the success-probability
curve implies the probability order needed by the left-tail binary LDP
certificate.
-/
theorem theorem31_ordered_quality_pair_compactSuperset_successProb_snd_le_fst_of_mono_of_index_snd_succ_le_fst
    {n : ℕ} {cut : ℕ → ℝ} (hmono : Monotone cut)
    {piece : Fin n × Fin n}
    (hindex : piece.2.val + 1 ≤ piece.1.val)
    {successProb : ℝ → ℝ} (hprob_mono : Monotone successProb) :
    ∀ q : ℝ × ℝ,
      q ∈ theorem31_ordered_quality_pair_compactSuperset n cut piece →
        successProb q.2 ≤ successProb q.1 := by
  intro q hq
  exact hprob_mono
    (theorem31_ordered_quality_pair_compactSuperset_snd_le_fst_of_index_snd_succ_le_fst
      hmono hindex q hq)

/--
Lemma C.3 ordered-rectangle decomposition: for a stepwise `β` represented by
monotone quality cutpoints, exact rate certificates on every selected
rectangle aggregate to the minimum selected rectangle exponent.
-/
theorem lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_min_component_certificates
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (errorKernel : ℕ → ℝ × ℝ → ℝ)
    (rate : {piece : Fin n × Fin n // selected piece} → ℝ)
    (hcomponent_int :
      ∀ k component,
        IntegrableOn (errorKernel k)
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ =>
            (theorem31_ordered_quality_pair_partition μ n cut hmono selected).componentIntegral
              (errorKernel k) component)
          (rate component))
    (minComponent : {piece : Fin n × Fin n // selected piece})
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ n cut hmono selected).support,
          errorKernel k x ∂(μ.prod μ))
      (rate minComponent) :=
  lemmaC3_partition_integral_hasExponentialRate_of_min_component_certificates
    (μ.prod μ)
    (theorem31_ordered_quality_pair_partition μ n cut hmono selected)
    errorKernel rate hcomponent_int hcert minComponent hrate_ge

/--
Lemma C.3 ordered-rectangle adjacent-dominance bridge: for a stepwise `β`
represented by monotone quality cutpoints, a selected adjacent rectangle
subfamily that dominates all selected rectangles determines the exponent of
the continuum pairwise error integral over those rectangles.
-/
theorem lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily
    {Adjacent : Type*}
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (errorKernel : ℕ → ℝ × ℝ → ℝ)
    (rate : {piece : Fin n × Fin n // selected piece} → ℝ)
    (selectAdjacent : Adjacent → {piece : Fin n × Fin n // selected piece})
    (hcomponent_int :
      ∀ k component,
        IntegrableOn (errorKernel k)
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ =>
            (theorem31_ordered_quality_pair_partition μ n cut hmono selected).componentIntegral
              (errorKernel k) component)
          (rate component))
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ n cut hmono selected).support,
          errorKernel k x ∂(μ.prod μ))
      (rate (selectAdjacent minAdjacent)) :=
  lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily
    (μ.prod μ)
    (theorem31_ordered_quality_pair_partition μ n cut hmono selected)
    errorKernel rate selectAdjacent hcomponent_int hcert minAdjacent
    hadj_min hadj_dominates

/--
Lemma C.3 selected ordered-pair partition-integral aggregation for the
endpoint-pair convention in the source proof. The kernel is constant on each
selected ordered rectangle and equal to that component's finite endpoint error;
the component certificates and adjacent-dominance reduction are discharged.
-/
theorem lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min
    (μ : Measure ℝ)
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ))
    (minAdjacent : Fin (m + 1))
    (hweight_pos :
      0 <
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet
              (theorem31OrderedAdjacentPiece hm minAdjacent),
          weight x ∂(μ.prod μ))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x *
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                (fun component k =>
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb hprob0 hprob1) sampleRate
                    component.val.2 component.val.1 k)
                k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let P :=
    theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
  let componentError : theorem31OrderedNontrivialPairComponent m → ℕ → ℝ :=
    fun component k =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate
        component.val.2 component.val.1 k
  let rate : theorem31OrderedNontrivialPairComponent m → ℝ :=
    fun component =>
      binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2
  let selectAdjacent : Fin (m + 1) → theorem31OrderedNontrivialPairComponent m :=
    theorem31OrderedAdjacentPiece hm
  have hcert :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ExponentialRateCertificate
          (componentError component) (rate component) := by
    intro component
    exact
      binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair
        successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hprob_mono
        hprob_pos_of_not_first hprob_lt_one_of_not_last hsample_pos component
  have hsub_min :
      ∀ adj : Fin (m + 1),
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj) := by
    intro adj
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj_min adj
  have hdominates :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        ∃ adj : Fin (m + 1), rate (selectAdjacent adj) ≤ rate component := by
    intro component
    rcases
      theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
        sampleRate successProb hsample_pos hsample_mono hprob_mono hprob0
        hprob_pos_of_not_first hprob_lt_one_of_not_last component with
      ⟨adj, hadj⟩
    refine ⟨adj, ?_⟩
    simpa [rate, selectAdjacent, theorem31OrderedAdjacentPiece,
      binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hadj
  have hresult :=
    P.setIntegral_weightedPiecewiseConstKernel_hasExponentialRate_of_dominating_subfamily_certificates
      (weight := weight) (p := componentError) (rate := rate)
      (selectAdjacent := selectAdjacent)
      (by simpa [P] using hweight_int)
      (by simpa [P] using hweight_nonneg)
      hcert minAdjacent
      (by simpa [P, selectAdjacent] using hweight_pos)
      hsub_min hdominates
  simpa [P, componentError, rate, selectAdjacent, theorem31OrderedAdjacentPiece,
    binaryEndpointAwarePairRate_adjacent_eq_adjacentRate] using hresult

/--
Lemma C.3 selected ordered-pair partition-integral aggregation with the
paper's endpoint-level-vector convention discharging the finite binary-model
side conditions.
-/
theorem lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_of_endpointLevelVector
    (μ : Measure ℝ)
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ))
    (minAdjacent : Fin (m + 1))
    (hweight_pos :
      0 <
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet
              (theorem31OrderedAdjacentPiece hm minAdjacent),
          weight x ∂(μ.prod μ))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x *
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                (fun component k =>
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb
                      (BinaryEndpointLevelVector_nonneg hlevels)
                      (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                    component.val.2 component.val.1 k)
                k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min
    μ hm cut hmono successProb sampleRate
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_le_one hlevels)
    hlevels.1 hlevels.2.1 hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight hweight_int hweight_nonneg minAdjacent hweight_pos hadj_min

/--
Lemma C.3 selected ordered-pair partition-integral aggregation with local
positive objective weights.  The source proof only needs the objective density
to be nonnegative on cells and positive at the minimizing adjacent rectangle;
the positive component integral is derived from continuity and the
closure-of-interior support of the ordered rectangles.
-/
theorem lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x *
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                (fun component k =>
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb hprob0 hprob1) sampleRate
                    component.val.2 component.val.1 k)
                k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) := by
  let P :=
    theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
  have hweight_nonneg_integral :
      ∀ component,
        0 ≤
          ∫ x in P.pieceSet component, weight x ∂(μ.prod μ) := by
    intro component
    exact setIntegral_nonneg_of_ae_restrict (by simpa [P] using hweight_nonneg component)
  have hweight_pos_integral :
      0 <
        ∫ x in P.pieceSet (theorem31OrderedAdjacentPiece hm minAdjacent),
          weight x ∂(μ.prod μ) := by
    have hclosure :
        x0 (theorem31OrderedAdjacentPiece hm minAdjacent) ∈
          closure (interior (P.pieceSet (theorem31OrderedAdjacentPiece hm minAdjacent))) := by
      simpa [P] using
        theorem31_ordered_quality_pair_piece_mem_closure_interior
          μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))
          (theorem31OrderedAdjacentPiece hm minAdjacent)
          (hx0_mem (theorem31OrderedAdjacentPiece hm minAdjacent))
    exact
      FiniteMeasurableSetPartition.setIntegral_pos_of_ae_nonneg_of_continuousAt_pos_at_closure_interior
        (μ := μ.prod μ)
        (s := P.pieceSet (theorem31OrderedAdjacentPiece hm minAdjacent))
        (P.measurable_piece (theorem31OrderedAdjacentPiece hm minAdjacent))
        (by simpa [P] using hweight_int (theorem31OrderedAdjacentPiece hm minAdjacent))
        (by simpa [P] using hweight_nonneg (theorem31OrderedAdjacentPiece hm minAdjacent))
        (hweight_cont (theorem31OrderedAdjacentPiece hm minAdjacent))
        (hweight_x0_pos (theorem31OrderedAdjacentPiece hm minAdjacent))
        hclosure
  exact
    lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min
      μ hm cut hmono successProb sampleRate hprob0 hprob1 hfirst_zero
      hlast_one hsample_pos hsample_mono hprob_mono hprob_pos_of_not_first
      hprob_lt_one_of_not_last weight
      (by simpa [P] using hweight_int)
      (by simpa [P] using hweight_nonneg_integral)
      minAdjacent
      (by simpa [P, theorem31OrderedAdjacentPiece] using hweight_pos_integral)
      hadj_min

/--
Lemma C.3 selected ordered-pair partition-integral aggregation with local
positive objective weights and endpoint/support facts supplied by
`BinaryEndpointLevelVector`.
-/
theorem lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x *
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                (fun component k =>
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb
                      (BinaryEndpointLevelVector_nonneg hlevels)
                      (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                    component.val.2 component.val.1 k)
                k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos
    μ hm cut hmono successProb sampleRate
    (BinaryEndpointLevelVector_nonneg hlevels)
    (BinaryEndpointLevelVector_le_one hlevels)
    hlevels.1 hlevels.2.1 hsample_pos hsample_mono
    (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels hab)
    (BinaryEndpointLevelVector_pos_of_not_first hlevels)
    (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
    weight hweight_int hweight_nonneg x0 hx0_mem hweight_cont
    hweight_x0_pos minAdjacent hadj_min

/--
Lemma C.3 selected ordered-pair partition-integral aggregation with canonical
cell midpoints.  Strict adjacent cutpoints supply the local positive-weight
witnesses required by the continuum C.3 aggregation theorem.
-/
theorem lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x *
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                (fun component k =>
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb
                      (BinaryEndpointLevelVector_nonneg hlevels)
                      (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                    component.val.2 component.val.1 k)
                k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_endpointLevelVector
    μ hm cut hmono successProb sampleRate hlevels hsample_pos hsample_mono
    weight hweight_int hweight_nonneg
    (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
    (fun component =>
      theorem31_ordered_quality_pair_component_midpoint_mem
        μ cut hmono hcut_strict component)
    (fun _component => hweight_cont.continuousAt)
    hweight_midpoint_pos minAdjacent hadj_min

/--
Continuum piecewise-constant Lemma C.4 forward direction.  For endpoint-aware
equalized binary levels, the selected ordered-rectangle continuum error
integral with the piecewise-constant endpoint-pair kernel has a positive
exponential rate, provided the objective weight is nonnegative on cells and
locally positive on the minimizing adjacent cell.
-/
theorem lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    ∃ c : ℝ, 0 < c ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x *
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                  (fun component k =>
                    twoSampleFloorPkComplementErrorProb
                      (binaryRatingModel successProb
                        (BinaryEndpointLevelVector_nonneg hlevels)
                        (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                      component.val.2 component.val.1 k)
                  k x ∂(μ.prod μ))
        c := by
  let minAdjacent : Fin (m + 1) := firstAdjacentIndex
  rcases
    heq.exists_pos_common_rate hm hlevels
      (fun i => hsample_pos (adjacentHighIndex i))
      (fun i => hsample_pos (adjacentLowIndex i)) with
    ⟨r, hrpos, hr⟩
  have hfirst_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent := by
    rw [hr minAdjacent]
    exact hrpos
  have hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj := by
    intro adj
    rw [hr minAdjacent, hr adj]
  refine
    ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent,
      hfirst_pos, ?_⟩
  simpa [minAdjacent] using
    lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos
      μ hm cut hmono successProb sampleRate
      (BinaryEndpointLevelVector_nonneg hlevels)
      (BinaryEndpointLevelVector_le_one hlevels)
      hlevels.1 hlevels.2.1 hsample_pos hsample_mono hprob_mono
      (BinaryEndpointLevelVector_pos_of_not_first hlevels)
      (BinaryEndpointLevelVector_lt_one_of_not_last hlevels)
      weight hweight_int hweight_nonneg x0 hx0_mem hweight_cont
      hweight_x0_pos minAdjacent hadj_min

/--
Continuum piecewise-constant Lemma C.4 forward direction with the success
probability monotonicity derived from `BinaryEndpointLevelVector`.
-/
theorem lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_endpointLevelVector
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    ∃ c : ℝ, 0 < c ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x *
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                  (fun component k =>
                    twoSampleFloorPkComplementErrorProb
                      (binaryRatingModel successProb
                        (BinaryEndpointLevelVector_nonneg hlevels)
                        (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                      component.val.2 component.val.1 k)
                  k x ∂(μ.prod μ))
        c := by
  let minAdjacent : Fin (m + 1) := firstAdjacentIndex
  rcases
    heq.exists_pos_common_rate hm hlevels
      (fun i => hsample_pos (adjacentHighIndex i))
      (fun i => hsample_pos (adjacentLowIndex i)) with
    ⟨r, hrpos, hr⟩
  have hfirst_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent := by
    rw [hr minAdjacent]
    exact hrpos
  have hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj := by
    intro adj
    rw [hr minAdjacent, hr adj]
  refine
    ⟨binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent,
      hfirst_pos, ?_⟩
  simpa [minAdjacent] using
    lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_endpointLevelVector
      μ hm cut hmono successProb sampleRate hlevels hsample_pos hsample_mono
      weight hweight_int hweight_nonneg x0 hx0_mem hweight_cont
      hweight_x0_pos minAdjacent hadj_min

/--
Continuum Lemma C.4 forward direction with the equalized endpoint levels
constructed from the source's forward-clipped shooting argument. Positive
endpoint sample rates give the unique endpoint-normalized equalized level
vector; the ordered-rectangle piecewise-constant continuum objective then has
a positive exponential rate.
-/
theorem lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ∃ c : ℝ, 0 < c ∧
            HasExponentialRate
              (fun k : ℕ =>
                ∫ x in
                  (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                    (theorem31OrderedNontrivialPairSelected (m := m))).support,
                  weight x *
                    (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                      (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                        (fun component k =>
                          twoSampleFloorPkComplementErrorProb
                            (binaryRatingModel levels
                              (BinaryEndpointLevelVector_nonneg hlevels)
                              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                            component.val.2 component.val.1 k)
                        k x ∂(μ.prod μ))
              c := by
  have hsample_all : ∀ idx : Fin (m + 2), 0 < sampleRate idx := by
    intro idx
    have hraw : 0 < binaryEndpointSampleRateNat sampleRate idx.val :=
      hsample_pos idx.val idx.isLt
    rw [binaryEndpointSampleRateNat_of_lt sampleRate idx.isLt] at hraw
    exact hraw
  rcases
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
      hm sampleRate hsample_pos with
    ⟨levels, hlevels, _huniq⟩
  refine ⟨levels, hlevels.1, hlevels.2, ?_⟩
  exact
    lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_endpointLevelVector
      μ (show 0 < m by omega) cut hmono levels sampleRate hlevels.1
      hsample_all hsample_mono weight hweight_int hweight_nonneg x0 hx0_mem
      hweight_cont hweight_x0_pos hlevels.2

/--
Source-facing Lemma C.4 forward wrapper: if the paper's `Wbar_k` sequence is
eventually the selected ordered-rectangle error integral, then the
piecewise-constant endpoint construction gives a positive exponential-rate
certificate for that source sequence.
-/
theorem lemmaC4_sourceWbar_has_positive_exponential_rate_of_endpoint_piecewiseConstKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sourceWbar : ℕ → ℝ)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate)
    (hsourceWbar_eq :
      (fun k : ℕ =>
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x *
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                (fun component k =>
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb
                      (BinaryEndpointLevelVector_nonneg hlevels)
                      (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                    component.val.2 component.val.1 k)
                k x ∂(μ.prod μ))
        =ᶠ[atTop] sourceWbar)
    (hsourceWbar_nonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ sourceWbar k) :
    ∃ c : ℝ, 0 < c ∧ ExponentialRateCertificate sourceWbar c := by
  rcases
    lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_endpointLevelVector
      μ hm cut hmono successProb sampleRate hlevels hsample_pos hsample_mono
      weight hweight_int hweight_nonneg x0 hx0_mem hweight_cont
      hweight_x0_pos heq with
    ⟨c, hc, hrate⟩
  refine ⟨c, hc, ?_⟩
  exact
    ExponentialRateCertificate.of_has_rate_of_eventually_nonneg_of_pos_rate
      (HasExponentialRate.congr hsourceWbar_eq hrate) hc hsourceWbar_nonneg

/--
Source-facing Lemma C.4 forward wrapper with the endpoint levels constructed
by the source's forward-clipped shooting argument.  If the paper's `Wbar_k`
sequence is eventually the selected ordered-rectangle error integral for the
constructed equalized levels, then `Wbar_k` has a positive exponential rate.
-/
theorem lemmaC4_sourceWbar_has_positive_exponential_rate_of_forward_clipped_endpoint_piecewiseConstKernel
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sourceWbar : ℕ → ℝ)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (hsourceWbar_eq :
      ∀ (levels : Fin (m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate →
          (fun k : ℕ =>
            ∫ x in
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).support,
              weight x *
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                    (fun component k =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel levels
                          (BinaryEndpointLevelVector_nonneg hlevels)
                          (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                        component.val.2 component.val.1 k)
                    k x ∂(μ.prod μ))
            =ᶠ[atTop] sourceWbar) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ∃ c : ℝ, 0 < c ∧ HasExponentialRate sourceWbar c := by
  rcases
    lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg x0 hx0_mem hweight_cont hweight_x0_pos with
    ⟨levels, hlevels, heq, c, hc, hrate⟩
  refine ⟨levels, hlevels, heq, c, hc, ?_⟩
  exact HasExponentialRate.congr (hsourceWbar_eq levels hlevels heq) hrate

/--
Continuum Lemma C.4 forward direction with canonical cell midpoints.  Strictly
increasing adjacent cutpoints provide the cell witness package needed by the
piecewise-constant continuum rate theorem.
-/
theorem lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ∃ c : ℝ, 0 < c ∧
            HasExponentialRate
              (fun k : ℕ =>
                ∫ x in
                  (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                    (theorem31OrderedNontrivialPairSelected (m := m))).support,
                  weight x *
                    (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                      (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                        (fun component k =>
                          twoSampleFloorPkComplementErrorProb
                            (binaryRatingModel levels
                              (BinaryEndpointLevelVector_nonneg hlevels)
                              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                            component.val.2 component.val.1 k)
                        k x ∂(μ.prod μ))
              c := by
  exact
    lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component => hweight_cont.continuousAt)
      hweight_midpoint_pos

/--
Theorem 3.1 fixed-discretization continuum bridge for the endpoint-aware
piecewise-constant model.  The source's forward-clipped construction gives an
endpoint-normalized level vector that is maximin-optimal for the finite
worst-adjacent rate objective, and the selected ordered-rectangle continuum
error integral has exponential rate exactly equal to that optimal objective.
-/
theorem theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate
            (fun k : ℕ =>
              ∫ x in
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).support,
                weight x *
                  (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                    (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                      (fun component k =>
                        twoSampleFloorPkComplementErrorProb
                          (binaryRatingModel levels
                            (BinaryEndpointLevelVector_nonneg hlevels)
                            (BinaryEndpointLevelVector_le_one hlevels))
                          sampleRate component.val.2 component.val.1 k)
                      k x ∂(μ.prod μ))
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  have hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentHigh sampleRate hsample_pos
  have hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentLow sampleRate hsample_pos
  have hsample_all : ∀ idx : Fin (m + 2), 0 < sampleRate idx := by
    intro idx
    have hraw : 0 < binaryEndpointSampleRateNat sampleRate idx.val :=
      hsample_pos idx.val idx.isLt
    rw [binaryEndpointSampleRateNat_of_lt sampleRate idx.isLt] at hraw
    exact hraw
  rcases
    binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
      hm sampleRate hsample_pos with
    ⟨levels, hlevels, _huniq⟩
  refine ⟨levels, hlevels.1, hlevels.2, ?_, ?_, ?_⟩
  · exact
      binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized
        (show 0 < m by omega) sampleRate levels hlevels.1
        hsample_high hsample_low hlevels.2
  · rcases
      hlevels.2.exists_pos_common_rate (show 0 < m by omega) hlevels.1
        hsample_high hsample_low with
      ⟨r, hrpos, hr⟩
    have hobj :
        binaryEndpointAwareAdjacentRateObjective levels sampleRate = r :=
      binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
        levels sampleRate r hr
    rw [hobj]
    exact hrpos
  · let minAdjacent : Fin (m + 1) := firstAdjacentIndex
    have hadj_min :
        ∀ adj : Fin (m + 1),
          binaryEndpointAwareAdjacentRate levels sampleRate minAdjacent ≤
            binaryEndpointAwareAdjacentRate levels sampleRate adj := by
      intro adj
      exact le_of_eq (hlevels.2 minAdjacent adj)
    have hrate :=
      lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos
        μ (show 0 < m by omega) cut hmono levels sampleRate
        (BinaryEndpointLevelVector_nonneg hlevels.1)
        (BinaryEndpointLevelVector_le_one hlevels.1)
        hlevels.1.1 hlevels.1.2.1 hsample_all hsample_mono
        (fun {_a _b} hab => BinaryEndpointLevelVector_mono hlevels.1 hab)
        (BinaryEndpointLevelVector_pos_of_not_first hlevels.1)
        (BinaryEndpointLevelVector_lt_one_of_not_last hlevels.1)
        weight hweight_int hweight_nonneg x0 hx0_mem hweight_cont
        hweight_x0_pos minAdjacent hadj_min
    have hobj :
        binaryEndpointAwareAdjacentRateObjective levels sampleRate =
          binaryEndpointAwareAdjacentRate levels sampleRate minAdjacent :=
      binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
        levels sampleRate hlevels.2 minAdjacent
    simpa [minAdjacent, hobj] using hrate

/--
Source-defined `Wbar_k` convention for Theorem 3.1's fixed-discretization
ordered-rectangle branch: integrate the selected piecewise-constant error
kernel over the source's ordered quality-pair partition.
-/
def theorem31SourceWbar
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (weight : ℝ × ℝ → ℝ) : ℕ → ℝ :=
  fun k : ℕ =>
    ∫ x in
      (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
        (theorem31OrderedNontrivialPairSelected (m := m))).support,
      weight x *
        (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
            (fun component k =>
              twoSampleFloorPkComplementErrorProb
                (binaryRatingModel levels
                  (BinaryEndpointLevelVector_nonneg hlevels)
                  (BinaryEndpointLevelVector_le_one hlevels))
                sampleRate component.val.2 component.val.1 k)
            k x ∂(μ.prod μ)

/--
The source-defined Theorem 3.1 `Wbar_k` is definitionally the selected
ordered-rectangle integral.
-/
theorem theorem31SourceWbar_eventually_eq
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (weight : ℝ × ℝ → ℝ) :
    (fun k : ℕ =>
      ∫ x in
        (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
          (theorem31OrderedNontrivialPairSelected (m := m))).support,
        weight x *
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
              (fun component k =>
                twoSampleFloorPkComplementErrorProb
                  (binaryRatingModel levels
                    (BinaryEndpointLevelVector_nonneg hlevels)
                    (BinaryEndpointLevelVector_le_one hlevels))
                  sampleRate component.val.2 component.val.1 k)
              k x ∂(μ.prod μ))
      =ᶠ[atTop]
        theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight := by
  filter_upwards with k
  rfl

/--
The source-defined Theorem 3.1 `Wbar_k` is nonnegative whenever the component
weight integrals are nonnegative.  This supplies the nonnegativity side needed
to turn positive exact rates into exact-rate certificates.
-/
theorem theorem31SourceWbar_nonneg
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg_integral :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ)) :
    ∀ k : ℕ,
      0 ≤ theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight k := by
  classical
  intro k
  let P :=
    theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
      (theorem31OrderedNontrivialPairSelected (m := m))
  let p : theorem31OrderedNontrivialPairComponent m → ℕ → ℝ :=
    fun component k =>
      twoSampleFloorPkComplementErrorProb
        (binaryRatingModel levels
          (BinaryEndpointLevelVector_nonneg hlevels)
          (BinaryEndpointLevelVector_le_one hlevels))
        sampleRate component.val.2 component.val.1 k
  simpa [theorem31SourceWbar, P, p] using
    P.setIntegral_weighted_piecewiseConstKernel_nonneg weight p k
      (by simpa [P] using hweight_int)
      (by simpa [P] using hweight_nonneg_integral)
      (fun component =>
        twoSampleFloorPkComplementErrorProb_nonneg
          (binaryRatingModel levels
            (BinaryEndpointLevelVector_nonneg hlevels)
            (BinaryEndpointLevelVector_le_one hlevels))
          sampleRate component.val.2 component.val.1 k)

/--
Eventual form of `theorem31SourceWbar_nonneg`.
-/
theorem theorem31SourceWbar_eventually_nonneg
    (μ : Measure ℝ) {m : ℕ} (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (levels : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector levels)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg_integral :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ)) :
    ∀ᶠ k : ℕ in atTop,
      0 ≤ theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight k :=
  Eventually.of_forall
    (theorem31SourceWbar_nonneg μ cut hmono sampleRate levels hlevels weight
      hweight_int hweight_nonneg_integral)

/--
Source-defined Theorem 3.1 fixed-discretization bridge.  This is the
source-`Wbar_k` form of the fixed ordered-rectangle rate theorem, with no
separate equality premise.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  rcases
    theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg x0 hx0_mem hweight_cont hweight_x0_pos with
    ⟨levels, hlevels, heq, hopt, hpos, hrate⟩
  refine ⟨levels, hlevels, heq, hopt, hpos, ?_⟩
  exact
    HasExponentialRate.congr
      (theorem31SourceWbar_eventually_eq μ cut hmono sampleRate levels
        hlevels weight)
      hrate

/--
Certificate form of the source-defined Theorem 3.1 fixed-discretization
bridge.  The source-defined `Wbar_k` is nonnegative by the finite partition
decomposition, so the positive exact rate upgrades to an exact-rate
certificate without an additional positivity premise.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  rcases
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg x0 hx0_mem hweight_cont hweight_x0_pos with
    ⟨levels, hlevels, heq, hopt, hpos, hrate⟩
  refine ⟨levels, hlevels, heq, hopt, hpos, ?_⟩
  have hweight_nonneg_integral :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ) := by
    intro component
    exact setIntegral_nonneg_of_ae_restrict (hweight_nonneg component)
  exact
    ExponentialRateCertificate.of_has_rate_of_eventually_nonneg_of_pos_rate
      hrate hpos
      (theorem31SourceWbar_eventually_nonneg μ cut hmono sampleRate levels
        hlevels weight hweight_int hweight_nonneg_integral)

/--
Fixed-discretization two-stage form of Theorem 3.1.  Once the interval
partition is fixed, every feasible endpoint vector has the same primary
limiting value; the forward-clipped endpoint construction is therefore
lexicographically optimal because it maximizes the adjacent-rate objective.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (limitingValue : ℝ) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun _candidate : Fin (m + 2) → ℝ => limitingValue)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels := by
  rcases
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg x0 hx0_mem hweight_cont hweight_x0_pos with
    ⟨levels, hlevels, heq, hopt, _hpos, hcert⟩
  refine ⟨levels, hlevels, heq, hcert, ?_⟩
  refine
    theorem31_two_stage_lexicographic_optimality_of_rate_maximizer_on_value_fiber
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun _candidate : Fin (m + 2) → ℝ => limitingValue)
      (fun candidate : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
      levels ?_ ?_
  · exact ⟨hlevels, by intro alt _halt; exact le_rfl⟩
  · refine ⟨⟨hlevels, rfl⟩, ?_⟩
    intro alt halt
    exact hopt.le halt.1

/--
Source-facing Theorem 3.1 fixed-discretization bridge.  The source's
forward-clipped construction gives endpoint levels that are maximin-optimal
for the finite adjacent-rate objective, and if the source `Wbar_k` sequence is
identified with the selected ordered-rectangle error integral for those
levels, then `Wbar_k` has the corresponding optimal exponential rate.
-/
theorem theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (sourceWbar : ℕ → ℝ)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (x0 : theorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (hsourceWbar_eq :
      ∀ (levels : Fin (m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate →
          (fun k : ℕ =>
            ∫ x in
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).support,
              weight x *
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                    (fun component k =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel levels
                          (BinaryEndpointLevelVector_nonneg hlevels)
                          (BinaryEndpointLevelVector_le_one hlevels))
                        sampleRate component.val.2 component.val.1 k)
                    k x ∂(μ.prod μ))
            =ᶠ[atTop] sourceWbar) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate sourceWbar
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  rcases
    theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg x0 hx0_mem hweight_cont hweight_x0_pos with
    ⟨levels, hlevels, heq, hopt, hpos, hrate⟩
  refine ⟨levels, hlevels, heq, hopt, hpos, ?_⟩
  exact HasExponentialRate.congr (hsourceWbar_eq levels hlevels heq) hrate

/--
Theorem 3.1 fixed-discretization continuum bridge with canonical cell
midpoints.  Strictly increasing adjacent cutpoints provide an interior witness
for every selected ordered rectangle, so the bridge no longer needs an
externally supplied witness function.
-/
theorem theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate
            (fun k : ℕ =>
              ∫ x in
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).support,
                weight x *
                  (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                    (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                      (fun component k =>
                        twoSampleFloorPkComplementErrorProb
                          (binaryRatingModel levels
                            (BinaryEndpointLevelVector_nonneg hlevels)
                            (BinaryEndpointLevelVector_le_one hlevels))
                          sampleRate component.val.2 component.val.1 k)
                      k x ∂(μ.prod μ))
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  exact
    theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component => hweight_cont.continuousAt)
      hweight_midpoint_pos

/--
Source-defined Theorem 3.1 fixed-discretization bridge with canonical cell
midpoints.  Strictly increasing adjacent cutpoints supply the
ordered-rectangle witnesses internally, and the source-defined `Wbar_k`
removes the arbitrary source-identification premise.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  exact
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component => hweight_cont.continuousAt)
      hweight_midpoint_pos

/--
Certificate form of the source-defined Theorem 3.1 fixed-discretization bridge
with canonical cell midpoints.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component)) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  exact
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component => hweight_cont.continuousAt)
      hweight_midpoint_pos

/--
Fixed-discretization two-stage form of Theorem 3.1 with canonical cell
midpoints.  Strictly increasing adjacent cutpoints provide an interior witness
for every selected ordered rectangle, so the weighted source-defined
lexicographic theorem no longer needs an externally supplied witness function.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component))
    (limitingValue : ℝ) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels weight)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun _candidate : Fin (m + 2) → ℝ => limitingValue)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels := by
  exact
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate
      μ hm cut hmono sampleRate hsample_pos hsample_mono weight hweight_int
      hweight_nonneg
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component => hweight_cont.continuousAt)
      hweight_midpoint_pos
      limitingValue

/--
Source-facing Theorem 3.1 fixed-discretization bridge with canonical cell
midpoints.  Strictly increasing adjacent cutpoints supply the selected
ordered-rectangle witnesses internally.
-/
theorem theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sourceWbar : ℕ → ℝ)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_cont : Continuous weight)
    (hweight_midpoint_pos :
      ∀ component : theorem31OrderedNontrivialPairComponent m,
        0 < weight
          (theorem31_ordered_quality_pair_component_midpoint (m := m) cut
            component))
    (hsourceWbar_eq :
      ∀ (levels : Fin (m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate →
          (fun k : ℕ =>
            ∫ x in
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).support,
              weight x *
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                    (fun component k =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel levels
                          (BinaryEndpointLevelVector_nonneg hlevels)
                          (BinaryEndpointLevelVector_le_one hlevels))
                        sampleRate component.val.2 component.val.1 k)
                    k x ∂(μ.prod μ))
            =ᶠ[atTop] sourceWbar) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate sourceWbar
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  exact
    theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
      μ hm cut hmono sourceWbar sampleRate hsample_pos hsample_mono weight
      hweight_int hweight_nonneg
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component => hweight_cont.continuousAt)
      hweight_midpoint_pos hsourceWbar_eq

/--
Theorem 3.1 fixed-discretization continuum bridge for the constant objective
weight `w ≡ 1`.  This is the Kendall-style source normalization where the
generic integrability, nonnegativity, continuity, and positive-witness weight
premises are discharged internally.
-/
theorem theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate
            (fun k : ℕ =>
              ∫ x in
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).support,
                (1 : ℝ) *
                  (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                    (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                      (fun component k =>
                        twoSampleFloorPkComplementErrorProb
                          (binaryRatingModel levels
                            (BinaryEndpointLevelVector_nonneg hlevels)
                            (BinaryEndpointLevelVector_le_one hlevels))
                          sampleRate component.val.2 component.val.1 k)
                      k x ∂(μ.prod μ))
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  simpa using
    theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
      μ hm cut hmono hcut_strict sampleRate hsample_pos hsample_mono
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        intro component
        simpa using
          (integrableOn_const (C := (1 : ℝ)) :
            IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ))
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
              (μ.prod μ)))
      (by
        intro component
        simp)
      continuous_const
      (by
        intro component
        norm_num)

/--
Source-defined Theorem 3.1 fixed-discretization bridge for the constant
objective weight `w ≡ 1`.  The source-defined `Wbar_k` removes the remaining
source-identification premise from the constant-weight branch.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels
              (fun _ : ℝ × ℝ => (1 : ℝ)))
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  simpa using
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
      μ hm cut hmono hcut_strict sampleRate hsample_pos hsample_mono
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        intro component
        simpa using
          (integrableOn_const (C := (1 : ℝ)) :
            IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ))
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
              (μ.prod μ)))
      (by
        intro component
        simp)
      continuous_const
      (by
        intro component
        norm_num)

/--
Certificate form of the source-defined Theorem 3.1 fixed-discretization bridge
for the constant objective weight `w ≡ 1`.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_const_weight_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels
              (fun _ : ℝ × ℝ => (1 : ℝ)))
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  simpa using
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
      μ hm cut hmono hcut_strict sampleRate hsample_pos hsample_mono
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        intro component
        simpa using
          (integrableOn_const (C := (1 : ℝ)) :
            IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ))
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
              (μ.prod μ)))
      (by
        intro component
        simp)
      continuous_const
      (by
        intro component
        norm_num)

/--
Fixed-discretization two-stage form of Theorem 3.1 for the normalized
constant-weight source convention.  Strictly increasing adjacent cutpoints
supply the selected ordered-rectangle witnesses internally; with the interval
partition fixed, all feasible endpoint vectors share the same primary value,
so the forward-clipped endpoint construction is lexicographically optimal by
maximizing the adjacent-rate objective.
-/
theorem theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate_const_weight_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (limitingValue : ℝ) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ExponentialRateCertificate
            (theorem31SourceWbar μ cut hmono sampleRate levels hlevels
              (fun _ : ℝ × ℝ => (1 : ℝ)))
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) ∧
          AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun _candidate : Fin (m + 2) → ℝ => limitingValue)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels := by
  simpa using
    theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate
      μ hm cut hmono sampleRate hsample_pos hsample_mono
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        intro component
        simpa using
          (integrableOn_const (C := (1 : ℝ)) :
            IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ))
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
              (μ.prod μ)))
      (by
        intro component
        simp)
      (theorem31_ordered_quality_pair_component_midpoint (m := m) cut)
      (fun component =>
        theorem31_ordered_quality_pair_component_midpoint_mem
          μ cut hmono hcut_strict component)
      (fun _component =>
        (continuous_const : Continuous (fun _ : ℝ × ℝ => (1 : ℝ))).continuousAt)
      (by
        intro component
        norm_num)
      limitingValue

/--
Source-facing Theorem 3.1 fixed-discretization bridge for the constant
objective weight `w ≡ 1`.  Besides the source identification of `Wbar_k`, all
ordered-rectangle witness and weight premises are discharged internally from
strictly increasing cutpoints.
-/
theorem theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 1 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (hcut_strict : ∀ i : ℕ, i < m + 2 → cut i < cut (i + 1))
    (sourceWbar : ℕ → ℝ)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hsourceWbar_eq :
      ∀ (levels : Fin (m + 2) → ℝ)
        (hlevels : BinaryEndpointLevelVector levels),
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate →
          (fun k : ℕ =>
            ∫ x in
              (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).support,
              (1 : ℝ) *
                (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                  (theorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                    (fun component k =>
                      twoSampleFloorPkComplementErrorProb
                        (binaryRatingModel levels
                          (BinaryEndpointLevelVector_nonneg hlevels)
                          (BinaryEndpointLevelVector_le_one hlevels))
                        sampleRate component.val.2 component.val.1 k)
                    k x ∂(μ.prod μ))
            =ᶠ[atTop] sourceWbar) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels ∧
          0 < binaryEndpointAwareAdjacentRateObjective levels sampleRate ∧
          HasExponentialRate sourceWbar
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  simpa using
    theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
      μ hm cut hmono hcut_strict sourceWbar sampleRate hsample_pos hsample_mono
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (by
        intro component
        simpa using
          (integrableOn_const (C := (1 : ℝ)) :
            IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ))
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (theorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
              (μ.prod μ)))
      (by
        intro component
        simp)
      continuous_const
      (by
        intro component
        norm_num)
      hsourceWbar_eq
end

end GJ19OptimalBinaryRatingSystems
