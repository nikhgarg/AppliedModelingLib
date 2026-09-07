import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Parity classes of finite subsets

A fixed element toggles membership and therefore exchanges odd- and
even-cardinality finite subsets.  The resulting equivalence gives the exact
half-count for subsets of a nonempty finite `Fin` type.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Math
namespace FinsetParity

/-- Odd-cardinality finite subsets. -/
abbrev OddFinsets (α : Type*) :=
  {s : Finset α // Odd s.card}

/-- Even-cardinality finite subsets. -/
abbrev EvenFinsets (α : Type*) :=
  {s : Finset α // Even s.card}

/-- Toggle membership of one designated element. -/
def toggleItem {α : Type*} [DecidableEq α] (a : α) (s : Finset α) : Finset α :=
  if a ∈ s then s.erase a else insert a s

theorem toggleItem_involutive {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) :
    toggleItem a (toggleItem a s) = s := by
  by_cases ha : a ∈ s <;> simp [toggleItem, ha]

theorem toggleItem_even {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (hs : Even s.card) :
    Odd (toggleItem a s).card := by
  by_cases ha : a ∈ s
  · rw [show (toggleItem a s).card = s.card - 1 by
      simp [toggleItem, ha, Finset.card_erase_of_mem ha]]
    exact Nat.Even.sub_odd (Finset.card_pos.mpr ⟨a, ha⟩) hs odd_one
  · rw [show (toggleItem a s).card = s.card + 1 by
      simp [toggleItem, ha]]
    exact hs.add_odd odd_one

theorem toggleItem_odd {α : Type*} [DecidableEq α]
    (a : α) (s : Finset α) (hs : Odd s.card) :
    Even (toggleItem a s).card := by
  by_cases ha : a ∈ s
  · rw [show (toggleItem a s).card = s.card - 1 by
      simp [toggleItem, ha, Finset.card_erase_of_mem ha]]
    rcases hs with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    omega
  · rw [show (toggleItem a s).card = s.card + 1 by
      simp [toggleItem, ha]]
    rcases hs with ⟨q, hq⟩
    refine ⟨q + 1, ?_⟩
    omega

/-- Toggling a fixed element exchanges odd- and even-cardinality subsets. -/
def oddEvenEquiv {α : Type*} [DecidableEq α] (a : α) :
    OddFinsets α ≃ EvenFinsets α where
  toFun := fun S => ⟨toggleItem a S.1, toggleItem_odd a S.1 S.2⟩
  invFun := fun S => ⟨toggleItem a S.1, toggleItem_even a S.1 S.2⟩
  left_inv := fun S => Subtype.ext (toggleItem_involutive a S.1)
  right_inv := fun S => Subtype.ext (toggleItem_involutive a S.1)

/-- Exactly half of the subsets of `Fin (k + 1)` have odd cardinality. -/
theorem card_oddFinsets_fin_succ (k : ℕ) :
    Fintype.card (OddFinsets (Fin (k + 1))) = 2 ^ k := by
  have hswap : Fintype.card (OddFinsets (Fin (k + 1))) =
      Fintype.card (EvenFinsets (Fin (k + 1))) :=
    Fintype.card_congr (oddEvenEquiv 0)
  have hcompl := Fintype.card_subtype_compl
    (α := Finset (Fin (k + 1))) (fun s => Odd s.card)
  have heven : Fintype.card (EvenFinsets (Fin (k + 1))) =
      Fintype.card (Finset (Fin (k + 1))) - Fintype.card (OddFinsets (Fin (k + 1))) := by
    simpa only [Nat.not_odd_iff_even] using hcompl
  have htotal : Fintype.card (Finset (Fin (k + 1))) = 2 ^ (k + 1) := by
    simp
  have hpows : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ]
    omega
  omega

end FinsetParity
end Math
end Foundations
end AppliedModelingLib
