import AppliedModelingLib.Foundations.Combinatorics.SteinerTriple
import AppliedModelingLib.Foundations.Graph.EvenPairing
import Mathlib.Data.Sym.Sym2

/-!
# Finite triangle packings and four-cycle leaves

Feder--Subi's near-decompositions use edge-disjoint triangles that may leave
a specified four-cycle uncovered.  This file keeps that exact finite object
separate from a Steiner triple system, whose pairs are all covered.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Combinatorics

open scoped Sym2

/-- A finite collection of literal triangles with no repeated unordered
edge. -/
structure TrianglePacking (α : Type) [Fintype α] [DecidableEq α] where
  Triangle : Type
  instFintypeTriangle : Fintype Triangle
  instDecidableEqTriangle : DecidableEq Triangle
  vertex : Triangle → Fin 3 → α
  vertex_injective : ∀ t, Function.Injective (vertex t)
  pair_covered_at_most_once : ∀ x y : α, x ≠ y → ∀ t u,
    (∃ i : Fin 3, vertex t i = x) → (∃ j : Fin 3, vertex t j = y) →
    (∃ i : Fin 3, vertex u i = x) → (∃ j : Fin 3, vertex u j = y) → t = u

attribute [instance] TrianglePacking.instFintypeTriangle
  TrianglePacking.instDecidableEqTriangle

namespace TrianglePacking

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Whether an ordered presentation of a non-loop pair is covered by a
triangle.  The condition is symmetric in its two point arguments. -/
def CoversPair (P : TrianglePacking α) (x y : α) : Prop :=
  ∃ t : P.Triangle,
    (∃ i : Fin 3, P.vertex t i = x) ∧ ∃ j : Fin 3, P.vertex t j = y

theorem coversPair_unique (P : TrianglePacking α) {x y : α} (hxy : x ≠ y)
    {t u : P.Triangle}
    (htx : ∃ i : Fin 3, P.vertex t i = x) (hty : ∃ j : Fin 3, P.vertex t j = y)
    (hux : ∃ i : Fin 3, P.vertex u i = x) (huy : ∃ j : Fin 3, P.vertex u j = y) :
    t = u :=
  P.pair_covered_at_most_once x y hxy t u htx hty hux huy

/-- Relabel a triangle packing along an equivalence of point sets. -/
def map {β : Type} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (P : TrianglePacking α) : TrianglePacking β where
  Triangle := P.Triangle
  instFintypeTriangle := P.instFintypeTriangle
  instDecidableEqTriangle := P.instDecidableEqTriangle
  vertex t i := e (P.vertex t i)
  vertex_injective t := e.injective.comp (P.vertex_injective t)
  pair_covered_at_most_once x y hxy t u htx hty hux huy := by
    apply P.pair_covered_at_most_once (e.symm x) (e.symm y)
      (fun h => hxy (by simpa using congrArg e h)) t u
    · rcases htx with ⟨i, hi⟩
      exact ⟨i, e.injective (by simpa using hi)⟩
    · rcases hty with ⟨j, hj⟩
      exact ⟨j, e.injective (by simpa using hj)⟩
    · rcases hux with ⟨i, hi⟩
      exact ⟨i, e.injective (by simpa using hi)⟩
    · rcases huy with ⟨j, hj⟩
      exact ⟨j, e.injective (by simpa using hj)⟩

/-- Characterize coverage after relabeling a triangle packing. -/
theorem map_coversPair_iff {β : Type} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (P : TrianglePacking α) (x y : β) :
    (P.map e).CoversPair x y ↔ P.CoversPair (e.symm x) (e.symm y) := by
  constructor
  · rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨t, ⟨i, e.injective (by simpa using hi)⟩,
      ⟨j, e.injective (by simpa using hj)⟩⟩
  · rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨t, ⟨i, by simpa using congrArg e hi⟩,
      ⟨j, by simpa using congrArg e hj⟩⟩

/-- Every Steiner triple system is, in particular, a triangle packing. -/
def ofSteinerTripleSystem (S : SteinerTripleSystem α) : TrianglePacking α where
  Triangle := S.Triangle
  instFintypeTriangle := S.instFintypeTriangle
  instDecidableEqTriangle := S.instDecidableEqTriangle
  vertex := S.vertex
  vertex_injective := S.vertex_injective
  pair_covered_at_most_once x y hxy t u htx hty hux huy := by
    exact (S.eq_triangleOfPair_of_contains x y hxy t htx hty).trans
      (S.eq_triangleOfPair_of_contains x y hxy u hux huy).symm

/-- The next vertex on the distinguished four-cycle. -/
def fourCycleNext (i : Fin 4) : Fin 4 :=
  ⟨(i.1 + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- A packing leaves exactly the four edges of an explicitly displayed
four-cycle when every other pair is covered. -/
def LeavesFourCycle (P : TrianglePacking α) (v : Fin 4 → α) : Prop :=
  Function.Injective v ∧ ∀ x y : α, x ≠ y →
    (P.CoversPair x y ↔ ¬ ∃ i : Fin 4, s(x, y) = s(v i, v (fourCycleNext i)))

/-- A triangle packing whose sole uncovered pairs form one perfect matching.
This is the natural intermediate object in the Feder--Subi `n ≡ 5 (mod 6)`
construction before every matching edge is expanded into a dense-split block. -/
structure WithMatchingLeave (α : Type) [Fintype α] [DecidableEq α] where
  packing : TrianglePacking α
  matching : AppliedModelingLib.Foundations.Graph.EvenPairing α
  coversPair_iff : ∀ x y : α, x ≠ y →
    (packing.CoversPair x y ↔ matching.perm x ≠ y)

/-- A triangle packing whose leave is the disjoint union of three perfect
matchings.  This is the natural macro object obtained by deleting one triple
from a Steiner triple system, and is used in Feder--Subi's final `r=5`
residue case. -/
structure WithThreeMatchingLeaves (α : Type) [Fintype α] [DecidableEq α] where
  packing : TrianglePacking α
  matching : Fin 3 → AppliedModelingLib.Foundations.Graph.EvenPairing α
  matching_edges_disjoint : ∀ i j : Fin 3, i ≠ j → ∀ x : α,
    (matching i).perm x ≠ (matching j).perm x
  coversPair_iff : ∀ x y : α, x ≠ y →
    (packing.CoversPair x y ↔ ∀ i : Fin 3, (matching i).perm x ≠ y)

/-- A triangle packing whose leave is the disjoint union of five perfect
matchings.  The five-point residual completion below turns this object into a
packing with a four-cycle leave. -/
structure WithFiveMatchingLeaves (α : Type) [Fintype α] [DecidableEq α] where
  packing : TrianglePacking α
  matching : Fin 5 → AppliedModelingLib.Foundations.Graph.EvenPairing α
  matching_edges_disjoint : ∀ i j : Fin 5, i ≠ j → ∀ x : α,
    (matching i).perm x ≠ (matching j).perm x
  coversPair_iff : ∀ x y : α, x ≠ y →
    (packing.CoversPair x y ↔ ∀ i : Fin 5, (matching i).perm x ≠ y)

/-- Relabel a three-matching leave along a finite equivalence. -/
def WithThreeMatchingLeaves.map {β : Type} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (L : WithThreeMatchingLeaves α) : WithThreeMatchingLeaves β where
  packing := L.packing.map e
  matching := fun i => (L.matching i).map e
  matching_edges_disjoint := by
    intro i j hij x h
    apply L.matching_edges_disjoint i j hij (e.symm x)
    apply e.injective
    change e ((L.matching i).perm (e.symm x)) = e ((L.matching j).perm (e.symm x))
    exact h
  coversPair_iff := by
    intro x y hxy
    have hxy' : e.symm x ≠ e.symm y := by
      intro h
      apply hxy
      simpa using congrArg e h
    rw [map_coversPair_iff e L.packing x y, L.coversPair_iff _ _ hxy']
    constructor
    · intro h i hi
      apply h i
      apply e.injective
      change e ((L.matching i).perm (e.symm x)) = e (e.symm y)
      calc
        e ((L.matching i).perm (e.symm x)) = ((L.matching i).map e).perm x := rfl
        _ = y := hi
        _ = e (e.symm y) := (e.apply_symm_apply y).symm
    · intro h i hi
      apply h i
      change e ((L.matching i).perm (e.symm x)) = y
      calc
        e ((L.matching i).perm (e.symm x)) =
            e (e.symm y) := congrArg e hi
        _ = y := e.apply_symm_apply y

/-- Relabeling preserves a specified four-cycle leave. -/
theorem map_leavesFourCycle {β : Type} [Fintype β] [DecidableEq β]
    (e : α ≃ β) (P : TrianglePacking α) (v : Fin 4 → α)
    (h : P.LeavesFourCycle v) :
    (P.map e).LeavesFourCycle (e ∘ v) := by
  constructor
  · exact e.injective.comp h.1
  · intro x y hxy
    have hxy' : e.symm x ≠ e.symm y := by
      intro h'
      apply hxy
      simpa using congrArg e h'
    have hcover : (P.map e).CoversPair x y ↔ P.CoversPair (e.symm x) (e.symm y) := by
      constructor
      · rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
        refine ⟨t, ⟨i, ?_⟩, ⟨j, ?_⟩⟩
        · apply e.injective
          simpa using hi
        · apply e.injective
          simpa using hj
      · rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨t, ⟨i, by simpa using congrArg e hi⟩,
          ⟨j, by simpa using congrArg e hj⟩⟩
    have hcycle :
        (∃ i : Fin 4, s(x, y) = s((e ∘ v) i, (e ∘ v) (fourCycleNext i))) ↔
          ∃ i : Fin 4, s(e.symm x, e.symm y) =
            s(v i, v (fourCycleNext i)) := by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        simpa only [Sym2.map_mk, Function.comp_apply, Equiv.symm_apply_apply] using
          congrArg (Sym2.map e.symm) hi
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        simpa only [Sym2.map_mk, Function.comp_apply, Equiv.apply_symm_apply] using
          congrArg (Sym2.map e) hi
    rw [hcover, h.2 (e.symm x) (e.symm y) hxy', hcycle]

private def finFiveVertex : Bool → Fin 3 → Fin 5
  | false, i => if i = 0 then 0 else if i = 1 then 1 else 2
  | true, i => if i = 0 then 0 else if i = 1 then 3 else 4

/-- The two edge-disjoint triangles in `K₅` whose leave is a four-cycle. -/
def finFive : TrianglePacking (Fin 5) where
  Triangle := Bool
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := finFiveVertex
  vertex_injective := by decide
  pair_covered_at_most_once := by decide

/-- The displayed leave of `finFive` is the cycle `1-3-2-4-1`. -/
def finFiveLeaveVertex (i : Fin 4) : Fin 5 :=
  if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 4

theorem finFive_leavesFourCycle : finFive.LeavesFourCycle finFiveLeaveVertex := by
  constructor
  · decide
  · intro x
    intro y
    intro hxy
    change (∃ t : Bool, (∃ i : Fin 3, finFiveVertex t i = x) ∧
      ∃ j : Fin 3, finFiveVertex t j = y) ↔
        ¬ ∃ i : Fin 4, s(x, y) = s(finFiveLeaveVertex i, finFiveLeaveVertex (fourCycleNext i))
    fin_cases x <;> fin_cases y
    all_goals first | exact False.elim (hxy rfl) | decide

/-- The finite `r = 5, t = 3` dense-split gadget in Feder--Subi's proof is
an explicit packing of `K₁₇` with a four-cycle leave.  We retain the 44
triangles as literal data, rather than assuming this finite base. -/
private abbrev finSeventeenVertex (t : Fin 44) (i : Fin 3) : Fin 17 :=
  let entry (a b c : Fin 17) : Fin 17 := if i = 0 then a else if i = 1 then b else c
  match t.1 with
  | 0 => entry 0 2 4
  | 1 => entry 0 5 6
  | 2 => entry 0 7 8
  | 3 => entry 0 9 10
  | 4 => entry 0 11 12
  | 5 => entry 0 13 14
  | 6 => entry 0 15 16
  | 7 => entry 2 5 7
  | 8 => entry 2 6 9
  | 9 => entry 2 8 11
  | 10 => entry 2 10 13
  | 11 => entry 2 12 15
  | 12 => entry 2 14 16
  | 13 => entry 1 5 10
  | 14 => entry 3 5 11
  | 15 => entry 4 5 14
  | 16 => entry 5 8 15
  | 17 => entry 5 9 12
  | 18 => entry 5 13 16
  | 19 => entry 1 8 9
  | 20 => entry 3 8 13
  | 21 => entry 6 8 14
  | 22 => entry 4 8 10
  | 23 => entry 8 12 16
  | 24 => entry 4 9 13
  | 25 => entry 3 9 16
  | 26 => entry 7 9 11
  | 27 => entry 9 14 15
  | 28 => entry 1 11 14
  | 29 => entry 6 11 13
  | 30 => entry 4 11 15
  | 31 => entry 10 11 16
  | 32 => entry 1 12 13
  | 33 => entry 7 13 15
  | 34 => entry 1 6 15
  | 35 => entry 3 10 15
  | 36 => entry 1 4 16
  | 37 => entry 1 3 7
  | 38 => entry 3 12 14
  | 39 => entry 3 4 6
  | 40 => entry 4 7 12
  | 41 => entry 6 10 12
  | 42 => entry 6 7 16
  | _ => entry 7 10 14

private abbrev FinThreeEdge := {p : Fin 3 × Fin 3 // p.1.1 < p.2.1}

private def orderedFinThreeEdge (i j : Fin 3) (hij : i ≠ j) : FinThreeEdge :=
  if h : i.1 < j.1 then ⟨(i, j), h⟩ else ⟨(j, i), by
    have hval : i.1 ≠ j.1 := Fin.val_injective.ne hij
    change j.1 < i.1
    omega⟩

private abbrev finSeventeenEdgeCode (q : Fin 44 × FinThreeEdge) : Sym2 (Fin 17) :=
  s(finSeventeenVertex q.1 q.2.1.1, finSeventeenVertex q.1 q.2.1.2)

private theorem finSeventeenEdgeCode_injective : Function.Injective finSeventeenEdgeCode := by
  set_option maxRecDepth 1000000 in
    decide

private theorem finSeventeenEdgeCode_ordered
    (t : Fin 44) (i j : Fin 3) (hij : i ≠ j) :
    finSeventeenEdgeCode (t, orderedFinThreeEdge i j hij) =
      s(finSeventeenVertex t i, finSeventeenVertex t j) := by
  unfold orderedFinThreeEdge
  split
  · rfl
  · exact Sym2.eq_swap

/-- The 44 literal triangles in the finite 17-point near-packing base. -/
def finSeventeen : TrianglePacking (Fin 17) where
  Triangle := Fin 44
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := finSeventeenVertex
  vertex_injective := by decide
  pair_covered_at_most_once := by
    intro x y hxy t u htx hty hux huy
    rcases htx with ⟨i, hi⟩
    rcases hty with ⟨j, hj⟩
    rcases hux with ⟨k, hk⟩
    rcases huy with ⟨l, hl⟩
    have hij : i ≠ j := by
      intro h
      apply hxy
      calc
        x = finSeventeenVertex t i := hi.symm
        _ = finSeventeenVertex t j := by rw [h]
        _ = y := hj
    have hkl : k ≠ l := by
      intro h
      apply hxy
      calc
        x = finSeventeenVertex u k := hk.symm
        _ = finSeventeenVertex u l := by rw [h]
        _ = y := hl
    have hcode : finSeventeenEdgeCode (t, orderedFinThreeEdge i j hij) =
        finSeventeenEdgeCode (u, orderedFinThreeEdge k l hkl) := by
      rw [finSeventeenEdgeCode_ordered, finSeventeenEdgeCode_ordered]
      calc
        s(finSeventeenVertex t i, finSeventeenVertex t j) = s(x, y) := by rw [hi, hj]
        _ = s(finSeventeenVertex u k, finSeventeenVertex u l) := by rw [hk, hl]
    exact congrArg Prod.fst (finSeventeenEdgeCode_injective hcode)

private def finSeventeenLeaveVertex (i : Fin 4) : Fin 17 := ⟨i.1, by omega⟩

theorem finSeventeen_leavesFourCycle :
    finSeventeen.LeavesFourCycle finSeventeenLeaveVertex := by
  constructor
  · intro i j hij
    apply Fin.ext
    simpa [finSeventeenLeaveVertex] using congrArg Fin.val hij
  · intro x y hxy
    change (∃ t : Fin 44, (∃ i : Fin 3, finSeventeenVertex t i = x) ∧
      ∃ j : Fin 3, finSeventeenVertex t j = y) ↔
        ¬ ∃ i : Fin 4, s(x, y) =
          s(finSeventeenLeaveVertex i, finSeventeenLeaveVertex (fourCycleNext i))
    fin_cases x <;> fin_cases y
    all_goals first | exact False.elim (hxy rfl) | decide

/-- The fixed `r=5,t=3` dense-split base used by Feder--Subi: five residual
vertices are independent, twelve clique vertices carry twelve internal
triangles, and each residual vertex is joined to a perfect matching of the
twelve clique vertices. -/
private abbrev DenseSplitFiveTwelveTriangle := Fin 12 ⊕ (Fin 5 × Fin 6)

private def denseSplitInternalVertex (t : Fin 12) (i : Fin 3) : Fin 12 :=
  let entry (a b c : Fin 12) : Fin 12 := if i = 0 then a else if i = 1 then b else c
  match t.1 with
  | 0 => entry 0 1 3
  | 1 => entry 4 10 11
  | 2 => entry 6 7 9
  | 3 => entry 2 5 8
  | 4 => entry 1 2 4
  | 5 => entry 0 5 9
  | 6 => entry 3 7 11
  | 7 => entry 6 8 10
  | 8 => entry 1 5 11
  | 9 => entry 2 9 10
  | 10 => entry 3 4 6
  | _ => entry 0 7 8

private def denseSplitMatchingVertex (q : Fin 5 × Fin 6) (i : Fin 3) :
    Fin 5 ⊕ Fin 12 :=
  let entry (a b : Fin 12) : Fin 5 ⊕ Fin 12 :=
    if i = 0 then Sum.inl q.1 else if i = 1 then Sum.inr a else Sum.inr b
  match q.1.1, q.2.1 with
  | 0, 0 => entry 0 10
  | 0, 1 => entry 1 7
  | 0, 2 => entry 2 6
  | 0, 3 => entry 3 5
  | 0, 4 => entry 4 9
  | 0, _ => entry 8 11
  | 1, 0 => entry 0 6
  | 1, 1 => entry 1 8
  | 1, 2 => entry 2 3
  | 1, 3 => entry 4 5
  | 1, 4 => entry 7 10
  | 1, _ => entry 9 11
  | 2, 0 => entry 0 4
  | 2, 1 => entry 1 6
  | 2, 2 => entry 2 11
  | 2, 3 => entry 3 10
  | 2, 4 => entry 5 7
  | 2, _ => entry 8 9
  | 3, 0 => entry 0 2
  | 3, 1 => entry 1 9
  | 3, 2 => entry 3 8
  | 3, 3 => entry 4 7
  | 3, 4 => entry 5 10
  | 3, _ => entry 6 11
  | _, 0 => entry 0 11
  | _, 1 => entry 1 10
  | _, 2 => entry 2 7
  | _, 3 => entry 3 9
  | _, 4 => entry 4 8
  | _, _ => entry 5 6

private def denseSplitFiveTwelveVertex
    (t : DenseSplitFiveTwelveTriangle) (i : Fin 3) : Fin 5 ⊕ Fin 12 :=
  match t with
  | Sum.inl q => Sum.inr (denseSplitInternalVertex q i)
  | Sum.inr q => denseSplitMatchingVertex q i

private abbrev denseSplitFiveTwelveEdgeCode
    (q : DenseSplitFiveTwelveTriangle × FinThreeEdge) : Sym2 (Fin 5 ⊕ Fin 12) :=
  s(denseSplitFiveTwelveVertex q.1 q.2.1.1, denseSplitFiveTwelveVertex q.1 q.2.1.2)

private theorem denseSplitFiveTwelveVertex_injective :
    ∀ t : DenseSplitFiveTwelveTriangle, Function.Injective (denseSplitFiveTwelveVertex t) := by
  decide

private theorem denseSplitFiveTwelveEdgeCode_injective :
    Function.Injective denseSplitFiveTwelveEdgeCode := by
  set_option maxRecDepth 1000000 in
    decide

private theorem denseSplitFiveTwelveEdgeCode_ordered
    (t : DenseSplitFiveTwelveTriangle) (i j : Fin 3) (hij : i ≠ j) :
    denseSplitFiveTwelveEdgeCode (t, orderedFinThreeEdge i j hij) =
      s(denseSplitFiveTwelveVertex t i, denseSplitFiveTwelveVertex t j) := by
  unfold orderedFinThreeEdge
  split
  · rfl
  · exact Sym2.eq_swap

/-- Literal `r=5,t=3` dense-split triangle packing.  It covers all clique
edges and all residual--clique edges, while deliberately using no edge within
the five-point residual side. -/
def denseSplitFiveTwelve : TrianglePacking (Fin 5 ⊕ Fin 12) where
  Triangle := DenseSplitFiveTwelveTriangle
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := denseSplitFiveTwelveVertex
  vertex_injective := denseSplitFiveTwelveVertex_injective
  pair_covered_at_most_once := by
    intro x y hxy t u htx hty hux huy
    rcases htx with ⟨i, hi⟩
    rcases hty with ⟨j, hj⟩
    rcases hux with ⟨k, hk⟩
    rcases huy with ⟨l, hl⟩
    have hij : i ≠ j := by
      intro h
      apply hxy
      calc
        x = denseSplitFiveTwelveVertex t i := hi.symm
        _ = denseSplitFiveTwelveVertex t j := by rw [h]
        _ = y := hj
    have hkl : k ≠ l := by
      intro h
      apply hxy
      calc
        x = denseSplitFiveTwelveVertex u k := hk.symm
        _ = denseSplitFiveTwelveVertex u l := by rw [h]
        _ = y := hl
    have hcode : denseSplitFiveTwelveEdgeCode (t, orderedFinThreeEdge i j hij) =
        denseSplitFiveTwelveEdgeCode (u, orderedFinThreeEdge k l hkl) := by
      rw [denseSplitFiveTwelveEdgeCode_ordered, denseSplitFiveTwelveEdgeCode_ordered]
      calc
        s(denseSplitFiveTwelveVertex t i, denseSplitFiveTwelveVertex t j) = s(x, y) := by
          rw [hi, hj]
        _ = s(denseSplitFiveTwelveVertex u k, denseSplitFiveTwelveVertex u l) := by
          rw [hk, hl]
    exact congrArg Prod.fst (denseSplitFiveTwelveEdgeCode_injective hcode)

theorem denseSplitFiveTwelve_covers_residual_clique (r : Fin 5) (s : Fin 12) :
    denseSplitFiveTwelve.CoversPair (Sum.inl r) (Sum.inr s) := by
  change ∃ t : DenseSplitFiveTwelveTriangle,
    (∃ i : Fin 3, denseSplitFiveTwelveVertex t i = Sum.inl r) ∧
      ∃ j : Fin 3, denseSplitFiveTwelveVertex t j = Sum.inr s
  fin_cases r <;> fin_cases s <;> decide

theorem denseSplitFiveTwelve_covers_clique_residual (s : Fin 12) (r : Fin 5) :
    denseSplitFiveTwelve.CoversPair (Sum.inr s) (Sum.inl r) := by
  rcases denseSplitFiveTwelve_covers_residual_clique r s with ⟨t, hr, hs⟩
  exact ⟨t, hs, hr⟩

/-- The dense-split block deliberately has no edge internal to its five-point
residual side; those edges are supplied by the separate residual packing. -/
theorem denseSplitFiveTwelve_not_covers_residual_pair (r s : Fin 5) (hrs : r ≠ s) :
    ¬ denseSplitFiveTwelve.CoversPair (Sum.inl r) (Sum.inl s) := by
  change ¬ ∃ t : DenseSplitFiveTwelveTriangle,
    (∃ i : Fin 3, denseSplitFiveTwelveVertex t i = Sum.inl r) ∧
      ∃ j : Fin 3, denseSplitFiveTwelveVertex t j = Sum.inl s
  fin_cases r <;> fin_cases s
  all_goals first | exact False.elim (hrs rfl) | decide

theorem denseSplitFiveTwelve_covers_clique_pair (s t : Fin 12) (hst : s ≠ t) :
    denseSplitFiveTwelve.CoversPair (Sum.inr s) (Sum.inr t) := by
  change ∃ q : DenseSplitFiveTwelveTriangle,
    (∃ i : Fin 3, denseSplitFiveTwelveVertex q i = Sum.inr s) ∧
      ∃ j : Fin 3, denseSplitFiveTwelveVertex q j = Sum.inr t
  fin_cases s <;> fin_cases t
  all_goals first | exact False.elim (hst rfl) | decide

end TrianglePacking

end Combinatorics
end Foundations
end AppliedModelingLib
