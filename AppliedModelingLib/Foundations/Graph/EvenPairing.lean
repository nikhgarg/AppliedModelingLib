import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Pairings of finite even types

An even finite set can be partitioned into disjoint unordered pairs.  The
interface below packages that elementary fact as a fixed-point-free
involution.  It is useful whenever an even-degree graph is represented by
pairing the incidences at each vertex.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

/-- A pairing of a type is a fixed-point-free involution.  Each two-element
orbit is one unordered pair. -/
structure EvenPairing (α : Type*) where
  perm : Equiv.Perm α
  apply_apply : ∀ x, perm (perm x) = x
  apply_ne : ∀ x, perm x ≠ x

namespace EvenPairing

variable {α : Type*}

/-- Relabel a pairing along an equivalence of its carrier. -/
def map {β : Type*} (e : α ≃ β) (p : EvenPairing α) : EvenPairing β where
  perm := (e.symm.trans p.perm).trans e
  apply_apply := by
    intro x
    change e (p.perm (e.symm (e (p.perm (e.symm x))))) = x
    rw [e.symm_apply_apply, p.apply_apply, e.apply_symm_apply]
  apply_ne := by
    intro x h
    apply p.apply_ne (e.symm x)
    apply e.injective
    change e (p.perm (e.symm x)) = e (e.symm x)
    calc
      e (p.perm (e.symm x)) = x := h
      _ = e (e.symm x) := (e.apply_symm_apply x).symm

theorem map_apply {β : Type*} (e : α ≃ β) (p : EvenPairing α) (x : β) :
    (p.map e).perm x = e (p.perm (e.symm x)) := rfl

/-- Swapping the two copies of `Fin k` gives the canonical pairing of
`Fin (k + k)`. -/
def finPair (k : ℕ) : Equiv.Perm (Fin (k + k)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin k) (Fin k))).trans
    finSumFinEquiv

theorem finPair_apply_apply (k : ℕ) (x : Fin (k + k)) :
    finPair k (finPair k x) = x := by
  simp [finPair]

theorem finPair_apply_ne (k : ℕ) (x : Fin (k + k)) :
    finPair k x ≠ x := by
  intro h
  have h' := congrArg finSumFinEquiv.symm h
  have h'' : Sum.swap (finSumFinEquiv.symm x) = finSumFinEquiv.symm x := by
    simpa [finPair] using h'
  cases hx : finSumFinEquiv.symm x with
  | inl i => simp [hx] at h''
  | inr i => simp [hx] at h''

/-- The canonical pairing of `Fin (k + k)`. -/
def fin (k : ℕ) : EvenPairing (Fin (k + k)) where
  perm := finPair k
  apply_apply := finPair_apply_apply k
  apply_ne := finPair_apply_ne k

/-- Every finite type with even cardinality has a pairing.  The construction
transports the canonical half-swap along a finite equivalence; it does not
choose or assume a graph-theoretic cycle decomposition. -/
noncomputable def ofEvenCard [Fintype α] (h : Even (Fintype.card α)) :
    EvenPairing α := by
  classical
  let k := Classical.choose h
  have hk : Fintype.card α = k + k := Classical.choose_spec h
  let e : α ≃ Fin (k + k) := Fintype.equivFinOfCardEq hk
  exact
    { perm := (e.trans (finPair k)).trans e.symm
      apply_apply := by
        intro x
        apply e.injective
        simpa [Equiv.trans_apply] using finPair_apply_apply k (e x)
      apply_ne := by
        intro x hfixed
        apply finPair_apply_ne k (e x)
        have h := congrArg e hfixed
        simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using h }

/-- Terms paired by a fixed-point-free involution cancel when they have
opposite real values. -/
theorem sum_eq_zero_of_apply_neg [Fintype α] (p : EvenPairing α) (f : α → ℝ)
    (hneg : ∀ x, f (p.perm x) = -f x) :
    ∑ x, f x = 0 := by
  have hperm : (∑ x, f (p.perm x)) = ∑ x, f x :=
    Fintype.sum_equiv p.perm (fun x => f (p.perm x)) f (fun _ => rfl)
  have hsum : (∑ x, f x) = -(∑ x, f x) := by
    calc
      (∑ x, f x) = ∑ x, f (p.perm x) := hperm.symm
      _ = ∑ x, -f x := by
        apply Finset.sum_congr rfl
        intro x _
        exact hneg x
      _ = -(∑ x, f x) := by
        simpa only [Finset.sum_neg_distrib]
  linarith

end EvenPairing

end Graph
end Foundations
end AppliedModelingLib
