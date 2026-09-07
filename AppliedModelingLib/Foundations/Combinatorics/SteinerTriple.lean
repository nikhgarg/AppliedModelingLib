import Mathlib

/-!
# Finite Steiner triple systems

A Steiner triple system is a partition of the unordered pairs of a finite
point set into triples.  We keep an explicit cyclic ordering of each triple:
this is harmless combinatorial data, and lets downstream constructions turn a
triangle directly into an alternating six-cycle in an incidence graph.

The definition is deliberately independent of any particular graph or choice
model.  It is useful whenever a complete graph is decomposed into triangles.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Combinatorics

open scoped BigOperators

/-- A finite Steiner triple system, with a chosen cyclic enumeration of each
triple.  `pair_covered_once` says that every unordered pair of distinct points
lies in exactly one triangle. -/
structure SteinerTripleSystem (α : Type) [Fintype α] [DecidableEq α] where
  Triangle : Type
  instFintypeTriangle : Fintype Triangle
  instDecidableEqTriangle : DecidableEq Triangle
  vertex : Triangle → Fin 3 → α
  vertex_injective : ∀ t, Function.Injective (vertex t)
  pair_covered_once : ∀ x y : α, x ≠ y →
    ∃! t, (∃ i : Fin 3, vertex t i = x) ∧ (∃ j : Fin 3, vertex t j = y)

attribute [instance] SteinerTripleSystem.instFintypeTriangle
  SteinerTripleSystem.instDecidableEqTriangle

namespace SteinerTripleSystem

variable {α : Type} [Fintype α] [DecidableEq α]
variable (S : SteinerTripleSystem α)

/-- The finite support of an enumerated triangle. -/
def support (t : S.Triangle) : Finset α :=
  Finset.univ.image (S.vertex t)

theorem mem_support_iff (t : S.Triangle) (x : α) :
    x ∈ S.support t ↔ ∃ i : Fin 3, S.vertex t i = x := by
  simp [support]

theorem vertex_mem_support (t : S.Triangle) (i : Fin 3) :
    S.vertex t i ∈ S.support t := by
  exact (S.mem_support_iff t _).mpr ⟨i, rfl⟩

theorem support_card (t : S.Triangle) : (S.support t).card = 3 := by
  rw [support, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact S.vertex_injective t hij

theorem vertex_ne_of_ne {t : S.Triangle} {i j : Fin 3} (hij : i ≠ j) :
    S.vertex t i ≠ S.vertex t j := by
  exact fun h => hij (S.vertex_injective t h)

/-- The unique triangle containing a specified distinct pair. -/
noncomputable def triangleOfPair (x y : α) (hxy : x ≠ y) : S.Triangle :=
  (S.pair_covered_once x y hxy).choose

theorem pair_mem_triangleOfPair (x y : α) (hxy : x ≠ y) :
    (∃ i : Fin 3, S.vertex (S.triangleOfPair x y hxy) i = x) ∧
      (∃ j : Fin 3, S.vertex (S.triangleOfPair x y hxy) j = y) :=
  (S.pair_covered_once x y hxy).choose_spec.1

theorem eq_triangleOfPair_of_contains (x y : α) (hxy : x ≠ y) (t : S.Triangle)
    (hx : ∃ i : Fin 3, S.vertex t i = x)
    (hy : ∃ j : Fin 3, S.vertex t j = y) :
    t = S.triangleOfPair x y hxy := by
  exact (S.pair_covered_once x y hxy).choose_spec.2 t ⟨hx, hy⟩

/-- Relabel a Steiner triple system along an equivalence of point sets. -/
def map {β : Type} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (S : SteinerTripleSystem α) : SteinerTripleSystem β where
  Triangle := S.Triangle
  instFintypeTriangle := S.instFintypeTriangle
  instDecidableEqTriangle := S.instDecidableEqTriangle
  vertex t i := e (S.vertex t i)
  vertex_injective t := e.injective.comp (S.vertex_injective t)
  pair_covered_once x y hxy := by
    obtain ⟨t, ht, htuniq⟩ :=
      S.pair_covered_once (e.symm x) (e.symm y) (fun h => hxy (by simpa using congrArg e h))
    refine ⟨t, ?_, ?_⟩
    · constructor
      · rcases ht.1 with ⟨i, hi⟩
        exact ⟨i, by simpa using congrArg e hi⟩
      · rcases ht.2 with ⟨j, hj⟩
        exact ⟨j, by simpa using congrArg e hj⟩
    · intro t' ht'
      apply htuniq
      constructor
      · rcases ht'.1 with ⟨i, hi⟩
        exact ⟨i, e.injective (by simpa using hi)⟩
      · rcases ht'.2 with ⟨j, hj⟩
        exact ⟨j, e.injective (by simpa using hj)⟩

/-- The one-triple Steiner system on three points. -/
def finThree : SteinerTripleSystem (Fin 3) where
  Triangle := PUnit
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex _ i := i
  vertex_injective _ := Function.injective_id
  pair_covered_once x y hxy := by
    refine ⟨PUnit.unit, ?_, ?_⟩
    · exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    · intro t _
      exact Subsingleton.elim _ _

/-- The edge-free Steiner triple system on one point. -/
def finOne : SteinerTripleSystem (Fin 1) where
  Triangle := Empty
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := Empty.elim
  vertex_injective t := Empty.elim t
  pair_covered_once x y hxy := False.elim (hxy (Subsingleton.elim _ _))

end SteinerTripleSystem

end Combinatorics
end Foundations
end AppliedModelingLib
