import LG24ServiceLevelAgreements.SLA2026Model
import Mathlib.Tactic

/-!
# Active 2026 fixed-load reformulation

This module proves the constraint projection used by the active manuscript's
Proposition `prop:opt-reformulation`.  The original formulation keeps the
Borough capacities and GPS weights; the reduced formulation keeps only the
SLA thresholds.  No monotonicity, convexity, or objective assumption is used:
the theorem is equality of the feasible threshold sets.

The source writes the SLA constraint as
`-(C_b * phi_{k,b} - s_{k,b}) * z_{k,b} + a <= 0`; it is retained literally
below rather than hidden behind a theorem-shaped assumption.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Original fixed-load program -/

/-- The source decision variables, with the manuscript's `Category -> Borough`
orientation. -/
structure SLA2026OriginalFixedLoadPolicy (Category Borough : Type*) where
  delay : Category → Borough → Real
  gpsWeight : Category → Borough → Real
  boroughCapacity : Borough → Real

/-- Feasibility of one original-program policy in the active source notation. -/
structure SLA2026OriginalFixedLoadFeasible
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : Real) (admitted : Category → Borough → Real)
    (policy : SLA2026OriginalFixedLoadPolicy Category Borough) : Prop where
  delay_pos : ∀ k b, 0 < policy.delay k b
  gpsWeight_nonneg : ∀ k b, 0 ≤ policy.gpsWeight k b
  boroughCapacity_nonneg : ∀ b, 0 ≤ policy.boroughCapacity b
  sla : ∀ k b,
    -(policy.boroughCapacity b * policy.gpsWeight k b - admitted k b) *
        policy.delay k b + tail ≤ 0
  gps : ∀ b, (∑ k, policy.gpsWeight k b) ≤ 1
  budget : (∑ b, policy.boroughCapacity b) ≤ capacity

/-- A threshold vector is feasible for the original program when some GPS
weights and Borough capacities support it. -/
def sla2026OriginalFixedLoadFeasible
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail capacity : Real) (admitted : Category → Borough → Real)
    (delay : Category → Borough → Real) : Prop :=
  ∃ gpsWeight boroughCapacity,
    SLA2026OriginalFixedLoadFeasible tail capacity admitted
      { delay := delay
        gpsWeight := gpsWeight
        boroughCapacity := boroughCapacity }

/-! ## Exact projection to reciprocal capacity -/

/-- The active source's fixed-load program projects exactly to
`sla2026Feasible`.  The only mathematical primitive conditions needed for the
projection are positive `a` and nonnegative admitted rates. -/
theorem sla2026_original_fixed_load_feasible_iff
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category]
    {tail capacity : Real} {admitted delay : Category → Borough → Real}
    (htail : 0 < tail) (hadmitted : ∀ k b, 0 ≤ admitted k b) :
    sla2026OriginalFixedLoadFeasible tail capacity admitted delay ↔
      sla2026Feasible tail capacity admitted delay := by
  classical
  constructor
  · rintro ⟨gpsWeight, boroughCapacity, hpolicy⟩
    change (∀ k b, 0 < delay k b) ∧
      (∑ k, ∑ b, tail / delay k b) ≤
        sla2026ExcessCapacity capacity admitted
    refine ⟨hpolicy.delay_pos, ?_⟩
    have hcell : ∀ k b,
        tail / delay k b ≤
          boroughCapacity b * gpsWeight k b - admitted k b := by
      intro k b
      apply (div_le_iff₀ (hpolicy.delay_pos k b)).2
      linarith [hpolicy.sla k b]
    have hborough : ∀ b,
        (∑ k, tail / delay k b) ≤
          boroughCapacity b - ∑ k, admitted k b := by
      intro b
      calc
        (∑ k, tail / delay k b) ≤
            ∑ k, (boroughCapacity b * gpsWeight k b - admitted k b) := by
              exact Finset.sum_le_sum fun k _ => hcell k b
        _ = boroughCapacity b * (∑ k, gpsWeight k b) -
              ∑ k, admitted k b := by
              simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ ≤ boroughCapacity b * 1 - ∑ k, admitted k b := by
              exact sub_le_sub_right
                (mul_le_mul_of_nonneg_left
                  (hpolicy.gps b) (hpolicy.boroughCapacity_nonneg b)) _
        _ = boroughCapacity b - ∑ k, admitted k b := by ring
    calc
      (∑ k, ∑ b, tail / delay k b) =
          ∑ b, ∑ k, tail / delay k b := Finset.sum_comm
      _ ≤ ∑ b, (boroughCapacity b - ∑ k, admitted k b) := by
          exact Finset.sum_le_sum fun b _ => hborough b
      _ = (∑ b, boroughCapacity b) - ∑ b, ∑ k, admitted k b := by
          rw [Finset.sum_sub_distrib]
      _ ≤ capacity - ∑ b, ∑ k, admitted k b := by
          exact sub_le_sub_right hpolicy.budget _
      _ = sla2026ExcessCapacity capacity admitted := by
          unfold sla2026ExcessCapacity
          rw [show (∑ b, ∑ k, admitted k b) =
            ∑ k, ∑ b, admitted k b from Finset.sum_comm]
  · intro hreduced
    change (∀ k b, 0 < delay k b) ∧
      (∑ k, ∑ b, tail / delay k b) ≤
        sla2026ExcessCapacity capacity admitted at hreduced
    let boroughCapacity : Borough → Real :=
      fun b ↦ ∑ k, (admitted k b + tail / delay k b)
    let gpsWeight : Category → Borough → Real :=
      fun k b => (admitted k b + tail / delay k b) / boroughCapacity b
    have hterm_pos : ∀ k b, 0 < admitted k b + tail / delay k b := by
      intro k b
      exact add_pos_of_nonneg_of_pos (hadmitted k b)
        (div_pos htail (hreduced.1 k b))
    have hboroughCapacity_pos : ∀ b, 0 < boroughCapacity b := by
      intro b
      obtain ⟨k⟩ := (inferInstance : Nonempty Category)
      apply lt_of_lt_of_le (hterm_pos k b)
      exact Finset.single_le_sum
        (fun j _ => add_nonneg (hadmitted j b)
          (div_nonneg htail.le (hreduced.1 j b).le))
        (Finset.mem_univ k)
    refine ⟨gpsWeight, boroughCapacity, ?_⟩
    refine
      { delay_pos := hreduced.1
        gpsWeight_nonneg := ?_
        boroughCapacity_nonneg := fun b => (hboroughCapacity_pos b).le
        sla := ?_
        gps := ?_
        budget := ?_ }
    · intro k b
      unfold gpsWeight
      exact div_nonneg
        (add_nonneg (hadmitted k b)
          (div_nonneg htail.le (hreduced.1 k b).le))
        (hboroughCapacity_pos b).le
    · intro k b
      have hslack :
          boroughCapacity b * gpsWeight k b - admitted k b =
            tail / delay k b := by
        unfold gpsWeight
        field_simp [(hboroughCapacity_pos b).ne', (hreduced.1 k b).ne']
        ring
      have hbind : (tail / delay k b) * delay k b = tail := by
        field_simp [(hreduced.1 k b).ne']
      rw [hslack]
      nlinarith [hbind]
    · intro b
      have hcapacity_ne : boroughCapacity b ≠ 0 :=
        (hboroughCapacity_pos b).ne'
      have hsum : (∑ k, gpsWeight k b) = 1 := by
        have hcapacity_def :
            Finset.univ.sum (fun k : Category ↦
              admitted k b + tail / delay k b) =
              boroughCapacity b := rfl
        calc
          (∑ k, gpsWeight k b) =
              (∑ k, (admitted k b + tail / delay k b)) /
                boroughCapacity b := by
                  unfold gpsWeight
                  rw [← Finset.sum_div]
          _ = 1 := by
              rw [hcapacity_def]
              exact div_self hcapacity_ne
      exact hsum.le
    · have hreduced_borough_order :
          (∑ b, ∑ k, tail / delay k b) ≤
            capacity - ∑ b, ∑ k, admitted k b := by
        calc
          (∑ b, ∑ k, tail / delay k b) =
              ∑ k, ∑ b, tail / delay k b := Finset.sum_comm
          _ ≤ sla2026ExcessCapacity capacity admitted := hreduced.2
          _ = capacity - ∑ b, ∑ k, admitted k b := by
              unfold sla2026ExcessCapacity
              rw [show (∑ k, ∑ b, admitted k b) =
                ∑ b, ∑ k, admitted k b from Finset.sum_comm]
      calc
        (∑ b, boroughCapacity b) =
            (∑ b, ∑ k, admitted k b) +
              ∑ b, ∑ k, tail / delay k b := by
                simp only [boroughCapacity, Finset.sum_add_distrib]
        _ ≤ capacity := by linarith

/-- Source-facing form of Proposition `prop:opt-reformulation`.  The manuscript
assumes positive excess capacity; the feasible-set equality above is valid even
without that domain restriction. -/
theorem sla2026_opt_reformulation
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category]
    {tail capacity : Real} {admitted delay : Category → Borough → Real}
    (htail : 0 < tail) (hadmitted : ∀ k b, 0 ≤ admitted k b)
    (_hexcess : 0 < sla2026ExcessCapacity capacity admitted) :
    sla2026OriginalFixedLoadFeasible tail capacity admitted delay ↔
      sla2026Feasible tail capacity admitted delay :=
  sla2026_original_fixed_load_feasible_iff htail hadmitted

/-- With the same loss on SLA thresholds, the original and reciprocal-capacity
programs have exactly the same minimizers.  This is the optimization-level
form of the source's equivalent-program claim; it is stronger than needed for
the source's convex-loss wording. -/
theorem sla2026_original_fixed_load_minimizer_iff
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    [Nonempty Category]
    {tail capacity : Real} {admitted : Category → Borough → Real}
    (objective : (Category → Borough → Real) → Real)
    {delay : Category → Borough → Real}
    (htail : 0 < tail) (hadmitted : ∀ k b, 0 ≤ admitted k b) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (sla2026OriginalFixedLoadFeasible tail capacity admitted) objective delay ↔
      AppliedModelingLib.Optimization.IsMinimizerOn
        (sla2026Feasible tail capacity admitted) objective delay := by
  constructor
  · intro h
    constructor
    · exact (sla2026_original_fixed_load_feasible_iff htail hadmitted).mp h.1
    · intro other hother
      exact h.2 other
        ((sla2026_original_fixed_load_feasible_iff htail hadmitted).mpr hother)
  · intro h
    constructor
    · exact (sla2026_original_fixed_load_feasible_iff htail hadmitted).mpr h.1
    · intro other hother
      exact h.2 other
        ((sla2026_original_fixed_load_feasible_iff htail hadmitted).mp hother)

end

end LG24ServiceLevelAgreements
