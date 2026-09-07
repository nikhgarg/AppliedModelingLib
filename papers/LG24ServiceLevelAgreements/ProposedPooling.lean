import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Proposed theory: one-period pooling and all-request burden

This file formalizes elementary identities proposed for the revision of
*Redesigning Service Level Agreements*.  For a single period, `backlog b` is
the work available in Borough `b`, `share b * capacity` is that Borough's
fixed allocation, and a pooled server may use the full capacity across all
Boroughs.

The pooling opportunity has two equivalent exact descriptions.  It is total
fixed-allocation shortage minus system-wide shortage, or, when the fixed
shares sum to one, total fixed-allocation slack minus system-wide slack.  The
latter is the capacity stranded by the fixed Borough split.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

/-- The positive part of a real number, written `(x)₊` in the revision memo. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- Rewriting a minimum as its first argument minus unmet demand. -/
theorem min_eq_sub_positivePart (x y : ℝ) :
    min x y = x - positivePart (x - y) := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, positivePart, max_eq_right (sub_nonpos.mpr hxy)]
    ring
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx, positivePart, max_eq_left (sub_nonneg.mpr hyx)]
    ring

/-- The symmetric minimum identity, expressed in terms of unused capacity. -/
theorem min_eq_right_sub_positivePart (x y : ℝ) :
    min x y = y - positivePart (y - x) := by
  simpa [min_comm] using min_eq_sub_positivePart y x

/-- Total work served in one period when Borough `b` receives a fixed share of capacity. -/
def fixedShareServed {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ) : ℝ :=
  ∑ b, min (backlog b) (share b * capacity)

/-- Total work served in one period when all Borough backlogs share capacity. -/
def pooledServed {Borough : Type*} [Fintype Borough]
    (backlog : Borough → ℝ) (capacity : ℝ) : ℝ :=
  min (∑ b, backlog b) capacity

/-- The one-period service gain available from pooling Borough capacity. -/
def poolingOpportunity {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ) : ℝ :=
  pooledServed backlog capacity - fixedShareServed backlog share capacity

/--
The memo's exact one-period identity: the pooling opportunity is the sum of
Borough-level shortages, less the shortage that remains after pooling.

This algebraic form does not itself require the shares to sum to one; that
condition is needed to interpret the fixed allocations as a partition of the
pooled capacity and to deduce nonnegativity.
-/
theorem poolingOpportunity_eq_shortage {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ) :
    poolingOpportunity backlog share capacity =
      (∑ b, positivePart (backlog b - share b * capacity)) -
        positivePart ((∑ b, backlog b) - capacity) := by
  classical
  simp_rw [poolingOpportunity, pooledServed, fixedShareServed,
    min_eq_sub_positivePart, Finset.sum_sub_distrib]
  ring

/--
Exact stranded-capacity identity when the fixed Borough shares exhaust total
capacity.  It subtracts slack that would remain even under pooling from the
sum of slack stranded inside the fixed Borough allocations.
-/
theorem poolingOpportunity_eq_strandedCapacity {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    poolingOpportunity backlog share capacity =
      (∑ b, positivePart (share b * capacity - backlog b)) -
        positivePart (capacity - ∑ b, backlog b) := by
  classical
  have hallocated : ∑ b, share b * capacity = capacity := by
    rw [← Finset.sum_mul, hshares, one_mul]
  simp_rw [poolingOpportunity, pooledServed, fixedShareServed,
    min_eq_right_sub_positivePart, Finset.sum_sub_distrib]
  rw [hallocated]
  ring

/-- Fixed Borough shares cannot serve more work than a pooled server. -/
theorem fixedShareServed_le_pooledServed {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    fixedShareServed backlog share capacity ≤ pooledServed backlog capacity := by
  classical
  rw [fixedShareServed, pooledServed]
  apply le_min
  · exact Finset.sum_le_sum fun b _hb ↦ min_le_left (backlog b) (share b * capacity)
  · calc
      ∑ b, min (backlog b) (share b * capacity) ≤
          ∑ b, share b * capacity :=
        Finset.sum_le_sum fun b _hb ↦ min_le_right (backlog b) (share b * capacity)
      _ = capacity := by rw [← Finset.sum_mul, hshares, one_mul]

/-- The one-period gain from capacity pooling is nonnegative. -/
theorem poolingOpportunity_nonneg {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    0 ≤ poolingOpportunity backlog share capacity := by
  exact sub_nonneg.mpr (fixedShareServed_le_pooledServed backlog share capacity hshares)

/-- Direct form of nonnegativity as pooled service minus fixed-share service. -/
theorem pooledServed_sub_fixedShareServed_nonneg {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    0 ≤ pooledServed backlog capacity - fixedShareServed backlog share capacity := by
  simpa [poolingOpportunity] using
    poolingOpportunity_nonneg backlog share capacity hshares

/-! ## Exact strictness and zero-gain characterization -/

/-- Total local work in excess of the fixed Borough allocations. -/
def totalLocalShortage {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ) : ℝ :=
  ∑ b, positivePart (backlog b - share b * capacity)

/-- Total local fixed capacity left unused by Borough backlogs. -/
def totalLocalSlack {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ) : ℝ :=
  ∑ b, positivePart (share b * capacity - backlog b)

theorem positivePart_sub_positivePart_neg (x : ℝ) :
    positivePart x - positivePart (-x) = x := by
  by_cases hx : 0 ≤ x
  · simp [positivePart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positivePart, max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]

/-- Aggregate net backlog is total local shortage minus total local slack. -/
theorem totalBacklog_sub_capacity_eq_shortage_sub_slack
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    (∑ b, backlog b) - capacity =
      totalLocalShortage backlog share capacity -
        totalLocalSlack backlog share capacity := by
  classical
  have hallocated : ∑ b, share b * capacity = capacity := by
    rw [← Finset.sum_mul, hshares, one_mul]
  unfold totalLocalShortage totalLocalSlack
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ b, backlog b) - capacity =
        ∑ b, (backlog b - share b * capacity) := by
      rw [Finset.sum_sub_distrib, hallocated]
    _ = ∑ b, (positivePart (backlog b - share b * capacity) -
        positivePart (share b * capacity - backlog b)) := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [show share b * capacity - backlog b =
        -(backlog b - share b * capacity) by ring]
      exact (positivePart_sub_positivePart_neg _).symm

/--
Pooling gain is exactly the smaller of total locally stranded capacity and
total local shortage.
-/
theorem poolingOpportunity_eq_min_shortage_slack
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    poolingOpportunity backlog share capacity =
      min (totalLocalShortage backlog share capacity)
        (totalLocalSlack backlog share capacity) := by
  rw [poolingOpportunity_eq_shortage]
  rw [totalBacklog_sub_capacity_eq_shortage_sub_slack
    backlog share capacity hshares]
  exact (min_eq_sub_positivePart
    (totalLocalShortage backlog share capacity)
    (totalLocalSlack backlog share capacity)).symm

theorem totalLocalShortage_nonneg
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ) :
    0 ≤ totalLocalShortage backlog share capacity := by
  classical
  unfold totalLocalShortage positivePart
  exact Finset.sum_nonneg fun b _hb ↦ le_max_right _ _

theorem totalLocalSlack_nonneg
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ) :
    0 ≤ totalLocalSlack backlog share capacity := by
  classical
  unfold totalLocalSlack positivePart
  exact Finset.sum_nonneg fun b _hb ↦ le_max_right _ _

/-- Pooling is strictly valuable exactly when local slack and shortage coexist. -/
theorem poolingOpportunity_pos_iff_simultaneous_slack_shortage
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    0 < poolingOpportunity backlog share capacity ↔
      0 < totalLocalShortage backlog share capacity ∧
        0 < totalLocalSlack backlog share capacity := by
  rw [poolingOpportunity_eq_min_shortage_slack backlog share capacity hshares]
  exact lt_min_iff

/-- Zero pooling gain means that aggregate local shortage or aggregate slack vanishes. -/
theorem poolingOpportunity_eq_zero_iff_no_slack_or_no_shortage
    {Borough : Type*} [Fintype Borough]
    (backlog share : Borough → ℝ) (capacity : ℝ)
    (hshares : ∑ b, share b = 1) :
    poolingOpportunity backlog share capacity = 0 ↔
      totalLocalShortage backlog share capacity = 0 ∨
        totalLocalSlack backlog share capacity = 0 := by
  rw [poolingOpportunity_eq_min_shortage_slack backlog share capacity hshares]
  constructor
  · intro hmin
    by_cases hs : totalLocalShortage backlog share capacity ≤
        totalLocalSlack backlog share capacity
    · left
      simpa [min_eq_left hs] using hmin
    · right
      have hls : totalLocalSlack backlog share capacity ≤
          totalLocalShortage backlog share capacity := le_of_not_ge hs
      simpa [min_eq_right hls] using hmin
  · rintro (hs | hl)
    · rw [hs, min_eq_left (totalLocalSlack_nonneg backlog share capacity)]
    · rw [hl, min_eq_right (totalLocalShortage_nonneg backlog share capacity)]

/-! ## All-request burden and the fixed-load efficiency accounting identity -/

/--
Expected delay-equivalent burden per arriving request: inspected requests
incur `conditionalDelay`, and non-inspected requests incur `noninspectionPenalty`.
-/
def allRequestBurden (risk inspectionProbability conditionalDelay noninspectionPenalty : ℝ) :
    ℝ :=
  risk * (inspectionProbability * conditionalDelay +
    (1 - inspectionProbability) * noninspectionPenalty)

/-- One cell's contribution to the fixed-admitted-load efficiency objective. -/
def fixedLoadEfficiencyCellCost
    (arrival admitted risk conditionalDelay noninspectionPenalty : ℝ) : ℝ :=
  admitted * risk * conditionalDelay +
    (arrival - admitted) * risk * noninspectionPenalty

/--
When admitted load is inspection probability times arrival load, the cell's
fixed-load efficiency cost is arrival load times its all-request burden.
-/
theorem fixedLoadEfficiencyCellCost_eq_arrival_mul_allRequestBurden
    (arrival admitted risk inspectionProbability conditionalDelay noninspectionPenalty : ℝ)
    (hadmitted : admitted = inspectionProbability * arrival) :
    fixedLoadEfficiencyCellCost arrival admitted risk conditionalDelay noninspectionPenalty =
      arrival * allRequestBurden risk inspectionProbability conditionalDelay
        noninspectionPenalty := by
  rw [hadmitted]
  simp only [fixedLoadEfficiencyCellCost, allRequestBurden]
  ring

end LG24ServiceLevelAgreements
