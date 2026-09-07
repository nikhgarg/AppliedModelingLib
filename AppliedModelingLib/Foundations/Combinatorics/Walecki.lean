import AppliedModelingLib.Foundations.Combinatorics.OneFactorization
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Option

/-!
# Walecki one-factorizations

For an odd cyclic group, Walecki's construction pairs its points around a
distinguished extra point.  The resulting matchings factor the complete graph
on the group plus that point.  This is the construction used by
Feder--Subi (2012, Lemma 1) in their recursive triangle decompositions.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Combinatorics

namespace Walecki

variable {m : ℕ}

/-- The Walecki matching indexed by `i`: the distinguished point is paired
with `i`, and every remaining group point `x` is paired with `2i - x`. -/
def step (i : ZMod m) : Option (ZMod m) → Option (ZMod m)
  | none => some i
  | some x => if x = i then none else some (i + i - x)

private theorem reflection_ne_center {i x : ZMod m} (hxi : x ≠ i) :
    i + i - x ≠ i := by
  intro h
  apply hxi
  calc
    x = i + i - (i + i - x) := by abel
    _ = i + i - i := by rw [h]
    _ = i := by abel

theorem step_involutive (i : ZMod m) : Function.Involutive (step i) := by
  intro p
  cases p with
  | none => simp [step]
  | some x =>
      by_cases hxi : x = i
      · subst x
        simp [step]
      · have hreflection : i + i - x ≠ i := reflection_ne_center hxi
        simp [step, hxi, hreflection]

private theorem two_isUnit (hm : Odd m) : IsUnit (2 : ZMod m) :=
  ZMod.isUnit_iff_coprime 2 m |>.mpr (Nat.coprime_two_left.mpr hm)

private theorem reflection_ne_self {i x : ZMod m} (hm : Odd m) (hxi : x ≠ i) :
    i + i - x ≠ x := by
  intro h
  apply hxi
  apply (two_isUnit hm).mul_left_cancel
  calc
    (2 : ZMod m) * x = x + x := by ring
    _ = (i + i - x) + x := by rw [h]
    _ = i + i := by abel
    _ = (2 : ZMod m) * i := by ring

theorem step_ne_self (hm : Odd m) (i : ZMod m) (p : Option (ZMod m)) :
    step i p ≠ p := by
  cases p with
  | none => simp [step]
  | some x =>
      by_cases hxi : x = i
      · subst x
        simp [step]
      · simpa [step, hxi] using reflection_ne_self hm hxi

/-- The fixed-point-free involution forming Walecki's `i`th matching. -/
noncomputable def matching (hm : Odd m) (i : ZMod m) :
    AppliedModelingLib.Foundations.Graph.EvenPairing (Option (ZMod m)) where
  perm := (step_involutive i).toPerm (step i)
  apply_apply := step_involutive i
  apply_ne := step_ne_self hm i

private theorem two_mul_half (hm : Odd m) (x : ZMod m) :
    (2 : ZMod m) * (x * (2 : ZMod m)⁻¹) = x := by
  calc
    (2 : ZMod m) * (x * (2 : ZMod m)⁻¹) =
        x * ((2 : ZMod m) * (2 : ZMod m)⁻¹) := by ring
    _ = x := by rw [ZMod.mul_inv_of_unit _ (two_isUnit hm), mul_one]

private theorem half_add_self (hm : Odd m) (x y : ZMod m) :
    let i : ZMod m := (x + y) * (2 : ZMod m)⁻¹
    i + i = x + y := by
  dsimp
  calc
    (x + y) * (2 : ZMod m)⁻¹ + (x + y) * (2 : ZMod m)⁻¹ =
        (2 : ZMod m) * ((x + y) * (2 : ZMod m)⁻¹) := by ring
    _ = x + y := two_mul_half hm (x + y)

private theorem half_ne_left {x y : ZMod m} (hxy : x ≠ y) (hm : Odd m) :
    (x + y) * (2 : ZMod m)⁻¹ ≠ x := by
  intro h
  have hsum := half_add_self hm x y
  have hsum' : x + x = x + y := by simpa [h] using hsum
  apply hxy
  symm
  calc
    y = x + y - x := by abel
    _ = x + x - x := by rw [← hsum']
    _ = x := by abel

private theorem step_half_apply {x y : ZMod m} (hxy : x ≠ y) (hm : Odd m) :
    step ((x + y) * (2 : ZMod m)⁻¹) (some x) = some y := by
  have hne : (x + y) * (2 : ZMod m)⁻¹ ≠ x := half_ne_left hxy hm
  have hxi : x ≠ (x + y) * (2 : ZMod m)⁻¹ := hne.symm
  rw [step, if_neg hxi]
  congr 1
  have hsum := half_add_self hm x y
  calc
    (x + y) * (2 : ZMod m)⁻¹ + (x + y) * (2 : ZMod m)⁻¹ - x =
        x + y - x := by rw [hsum]
    _ = y := by abel

private theorem index_eq_half_of_step {x y i : ZMod m} (hxy : x ≠ y) (hm : Odd m)
    (hi : step i (some x) = some y) : i = (x + y) * (2 : ZMod m)⁻¹ := by
  have hxi : x ≠ i := by
    intro h
    subst i
    simpa [step] using hi
  have hreflection : i + i - x = y := by
    rw [step, if_neg hxi] at hi
    exact Option.some.inj hi
  apply (two_isUnit hm).mul_left_cancel
  calc
    (2 : ZMod m) * i = i + i := by ring
    _ = (i + i - x) + x := by abel
    _ = y + x := by rw [hreflection]
    _ = x + y := by ac_rfl
    _ = (2 : ZMod m) * ((x + y) * (2 : ZMod m)⁻¹) :=
      (two_mul_half hm (x + y)).symm

/-- Walecki's one-factorization: when `m` is odd, the complete graph on
`Option (ZMod m)` is partitioned into its `m` explicit perfect matchings. -/
noncomputable def oneFactorization [NeZero m] (hm : Odd m) :
    OneFactorization (Option (ZMod m)) (ZMod m) := by
  exact
    { matching := matching hm
      pair_covered_once := by
        intro p q hpq
        cases p with
        | none =>
            cases q with
            | none => exact False.elim (hpq rfl)
            | some y =>
                refine ⟨y, ?_, ?_⟩
                · rfl
                · intro i hi
                  change step i none = some y at hi
                  simpa [step] using Option.some.inj hi
        | some x =>
            cases q with
            | none =>
                refine ⟨x, ?_, ?_⟩
                · simp [matching, step]
                · intro i hi
                  change step i (some x) = none at hi
                  by_cases hxi : x = i
                  · exact hxi.symm
                  · simp [step, hxi] at hi
            | some y =>
                have hxy : x ≠ y := by
                  intro h
                  exact hpq (congrArg some h)
                refine ⟨(x + y) * (2 : ZMod m)⁻¹, ?_, ?_⟩
                · change step ((x + y) * (2 : ZMod m)⁻¹) (some x) = some y
                  exact step_half_apply hxy hm
                · intro i hi
                  change step i (some x) = some y at hi
                  exact index_eq_half_of_step hxy hm hi }

end Walecki

end Combinatorics
end Foundations
end AppliedModelingLib
