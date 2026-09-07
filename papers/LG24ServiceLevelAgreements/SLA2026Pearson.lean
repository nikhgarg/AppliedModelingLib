import LG24ServiceLevelAgreements.SLA2026Model
import Mathlib.Tactic

/-!
# Finite Pearson algebra for the active 2026 SLA model

The price-of-equity proposition uses a Pearson divergence between two
positive capacity-share vectors.  This module proves the finite algebra once,
with every positivity and normalization condition visible in the theorem
statements.  It contains no endpoint or queueing assumptions.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-- Sum of a finite category--Borough vector. -/
def sla2026VectorMass
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (value : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, value k b

/-- Finite vector mass is additive. -/
theorem sla2026VectorMass_add
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (left right : Category → Borough → ℝ) :
    sla2026VectorMass (fun k b ↦ left k b + right k b) =
      sla2026VectorMass left + sla2026VectorMass right := by
  classical
  unfold sla2026VectorMass
  simp_rw [Finset.sum_add_distrib]

/-- Finite vector mass respects subtraction. -/
theorem sla2026VectorMass_sub
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (left right : Category → Borough → ℝ) :
    sla2026VectorMass (fun k b ↦ left k b - right k b) =
      sla2026VectorMass left - sla2026VectorMass right := by
  classical
  unfold sla2026VectorMass
  simp_rw [Finset.sum_sub_distrib]

/-- Finite vector mass pulls out a scalar. -/
theorem sla2026VectorMass_smul
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (scalar : ℝ) (value : Category → Borough → ℝ) :
    sla2026VectorMass (fun k b ↦ scalar * value k b) =
      scalar * sla2026VectorMass value := by
  classical
  unfold sla2026VectorMass
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]

/-- A Pearson divergence with positive right-hand side is nonnegative. -/
theorem sla2026PearsonChiSquare_nonneg
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {left right : Category → Borough → ℝ}
    (hright : ∀ k b, 0 < right k b) :
    0 ≤ sla2026PearsonChiSquare left right := by
  unfold sla2026PearsonChiSquare
  exact Finset.sum_nonneg fun k _hk ↦
    Finset.sum_nonneg fun b _hb ↦
      div_nonneg (sq_nonneg (left k b - right k b)) (hright k b).le

/--
For probability vectors, the reverse-weighted square sum is exactly one plus
the Pearson chi-square divergence.
-/
theorem sla2026_square_div_eq_one_add_pearson
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {left right : Category → Borough → ℝ}
    (hleft : sla2026VectorMass left = 1)
    (hrightMass : sla2026VectorMass right = 1)
    (hright : ∀ k b, 0 < right k b) :
    (∑ k, ∑ b, left k b ^ 2 / right k b) =
      1 + sla2026PearsonChiSquare left right := by
  classical
  have hterm (k : Category) (b : Borough) :
      left k b ^ 2 / right k b =
        right k b + (left k b - right k b) ^ 2 / right k b +
          2 * (left k b - right k b) := by
    field_simp [(hright k b).ne']
    ring
  let squareQuotient : Category → Borough → ℝ :=
    fun k b ↦ left k b ^ 2 / right k b
  let divergenceTerm : Category → Borough → ℝ :=
    fun k b ↦ (left k b - right k b) ^ 2 / right k b
  let difference : Category → Borough → ℝ :=
    fun k b ↦ left k b - right k b
  have hmassDifference : sla2026VectorMass difference =
      sla2026VectorMass left - sla2026VectorMass right := by
    exact sla2026VectorMass_sub left right
  have hmassScaledDifference : sla2026VectorMass
      (fun k b ↦ 2 * difference k b) =
        2 * (sla2026VectorMass left - sla2026VectorMass right) := by
    rw [sla2026VectorMass_smul, hmassDifference]
  calc
    (∑ k, ∑ b, left k b ^ 2 / right k b) =
        sla2026VectorMass squareQuotient := rfl
    _ = sla2026VectorMass (fun k b ↦ right k b + divergenceTerm k b +
          2 * difference k b) := by
          apply Eq.symm
          unfold squareQuotient divergenceTerm difference
          apply Finset.sum_congr rfl
          intro k _hk
          apply Finset.sum_congr rfl
          intro b _hb
          exact (hterm k b).symm
    _ = sla2026VectorMass right + sla2026VectorMass divergenceTerm +
          sla2026VectorMass (fun k b ↦ 2 * difference k b) := by
          rw [sla2026VectorMass_add]
          rw [sla2026VectorMass_add]
    _ = sla2026VectorMass right + sla2026PearsonChiSquare left right +
          2 * (sla2026VectorMass left - sla2026VectorMass right) := by
          rw [hmassScaledDifference]
          rfl
    _ = 1 + sla2026PearsonChiSquare left right := by
          rw [hleft, hrightMass]
          ring

/-- A positive-right Pearson divergence vanishes exactly at equality. -/
theorem sla2026PearsonChiSquare_eq_zero_iff
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {left right : Category → Borough → ℝ}
    (hright : ∀ k b, 0 < right k b) :
    sla2026PearsonChiSquare left right = 0 ↔ left = right := by
  classical
  constructor
  · intro hzero
    have hterms : ∀ k b,
        (left k b - right k b) ^ 2 / right k b = 0 := by
      have hsum : ∑ k, ∑ b,
          (left k b - right k b) ^ 2 / right k b = 0 := by
        simpa [sla2026PearsonChiSquare] using hzero
      have houter := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_hk : k ∈ (Finset.univ : Finset Category)) ↦
          Finset.sum_nonneg fun b _hb ↦
            div_nonneg (sq_nonneg (left k b - right k b))
              (hright k b).le)).1 hsum
      intro k b
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun c (_hc : c ∈ (Finset.univ : Finset Borough)) ↦
          div_nonneg (sq_nonneg (left k c - right k c))
            (hright k c).le)).1
        (houter k (Finset.mem_univ k)) b (Finset.mem_univ b)
    funext k b
    have hsq : (left k b - right k b) ^ 2 = 0 := by
      exact (div_eq_zero_iff).1 (hterms k b) |>.resolve_right (hright k b).ne'
    have hsub : left k b - right k b = 0 := (sq_eq_zero_iff).1 hsq
    linarith
  · intro heq
    subst right
    simp [sla2026PearsonChiSquare]

/-- A feasible positive SLA threshold gives a positive capacity share. -/
theorem sla2026CapacityShare_pos
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity : ℝ} {admitted delay : Category → Borough → ℝ}
    (htail : 0 < tail)
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hdelay : ∀ k b, 0 < delay k b) :
    ∀ k b, 0 < sla2026CapacityShare tail capacity admitted delay k b := by
  intro k b
  unfold sla2026CapacityShare
  exact div_pos htail (mul_pos hexcess (hdelay k b))

/-- Binding reciprocal capacity makes the source shares sum to one. -/
theorem sla2026CapacityShare_mass_eq_one
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity : ℝ} {admitted delay : Category → Borough → ℝ}
    (hexcess : 0 < sla2026ExcessCapacity capacity admitted)
    (hbind : (∑ k, ∑ b, tail / delay k b) =
      sla2026ExcessCapacity capacity admitted) :
    sla2026VectorMass (sla2026CapacityShare tail capacity admitted delay) = 1 := by
  classical
  have hterm (k : Category) (b : Borough) :
      tail / (sla2026ExcessCapacity capacity admitted * delay k b) =
        (tail / delay k b) / sla2026ExcessCapacity capacity admitted := by
    field_simp [hexcess.ne']
  unfold sla2026VectorMass sla2026CapacityShare
  simp_rw [hterm]
  calc
    (∑ k, ∑ b, tail / delay k b /
        sla2026ExcessCapacity capacity admitted) =
        (∑ k, ∑ b, tail / delay k b) /
          sla2026ExcessCapacity capacity admitted := by
            simp only [Finset.sum_div]
    _ = 1 := by
      rw [hbind]
      field_simp [hexcess.ne']

end

end LG24ServiceLevelAgreements
