import AppliedModelingLib.Foundations.Combinatorics.SteinerTriple
import AppliedModelingLib.Foundations.Combinatorics.OneFactorization
import AppliedModelingLib.Foundations.Combinatorics.Walecki
import Mathlib.Data.Sym.Sym2

/-!
# Constructors for finite Steiner triple systems

This module contains source-faithful finite constructions for Steiner triple
systems.  The first construction developed here is the Walecki extension:
given a triple system on `α` and a one-factorization on a disjoint even set
`β` whose factors are indexed by `α`, it builds the triple system on
`α ⊕ β` used in Feder--Subi's recursive proof.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Combinatorics

open scoped Sym2

/-- A non-loop unordered pair.  Its two fields are a finite edge of the
complete graph, and the proof that it has two distinct endpoints. -/
abbrev OffDiagonalPair (α : Type*) := {e : Sym2 α // ¬ e.IsDiag}

namespace OffDiagonalPair

variable {α : Type*}

/-- A chosen first endpoint, used only to give an ordered presentation of an
unordered edge when it is made into an ordered Steiner triple. -/
noncomputable def first (e : OffDiagonalPair α) : α := e.1.out.1

/-- The other endpoint in the chosen presentation. -/
noncomputable def second (e : OffDiagonalPair α) : α := e.1.out.2

theorem mk_first_second (e : OffDiagonalPair α) : s(e.first, e.second) = e.1 := by
  change s(e.1.out.1, e.1.out.2) = e.1
  rw [Sym2.mk, e.1.out_eq]

theorem first_ne_second (e : OffDiagonalPair α) : e.first ≠ e.second := by
  intro h
  apply e.2
  rw [← e.mk_first_second]
  exact Sym2.mk_isDiag_iff.mpr h

theorem mem_iff_first_or_second (e : OffDiagonalPair α) (x : α) :
    x ∈ e.1 ↔ x = e.first ∨ x = e.second := by
  rw [← e.mk_first_second]
  simp

/-- The off-diagonal edge on two explicitly distinct points. -/
def mk (x y : α) (hxy : x ≠ y) : OffDiagonalPair α :=
  ⟨s(x, y), by simpa using hxy⟩

@[simp] theorem val_mk (x y : α) (hxy : x ≠ y) : (mk x y hxy).1 = s(x, y) := rfl

theorem mem_mk_left (x y : α) (hxy : x ≠ y) : x ∈ (mk x y hxy).1 := by
  simp [mk]

theorem mem_mk_right (x y : α) (hxy : x ≠ y) : y ∈ (mk x y hxy).1 := by
  simp [mk]

end OffDiagonalPair

namespace OneFactorization

variable {α ι : Type*} [Fintype α] [DecidableEq α]
variable (F : OneFactorization α ι)

/-- The factor of an unordered non-loop edge. -/
noncomputable def factorOfEdge (e : OffDiagonalPair α) : ι :=
  F.factorOfPair e.first e.second e.first_ne_second

theorem matching_factorOfEdge_first (e : OffDiagonalPair α) :
    (F.matching (F.factorOfEdge e)).perm e.first = e.second :=
  F.matching_factorOfPair e.first e.second e.first_ne_second

theorem matching_factorOfEdge_second (e : OffDiagonalPair α) :
    (F.matching (F.factorOfEdge e)).perm e.second = e.first := by
  rw [← F.matching_factorOfEdge_first e]
  exact (F.matching (F.factorOfEdge e)).apply_apply e.first

theorem factorOfEdge_eq_of_matching_first (e : OffDiagonalPair α) (i : ι)
    (hi : (F.matching i).perm e.first = e.second) : i = F.factorOfEdge e :=
  F.factorOfPair_eq_of_matching e.first_ne_second i hi

/-- The factor of the explicitly presented edge `s(x,y)` is the factor whose
matching pairs `x` with `y`, independent of the representative chosen by
`Sym2.out`. -/
theorem factorOfEdge_mk_eq (x y : α) (hxy : x ≠ y) (i : ι)
    (hi : (F.matching i).perm x = y) :
    i = F.factorOfEdge (OffDiagonalPair.mk x y hxy) := by
  let e : OffDiagonalPair α := OffDiagonalPair.mk x y hxy
  change i = F.factorOfEdge e
  apply F.factorOfEdge_eq_of_matching_first
  have he : s(e.first, e.second) = s(x, y) := by
    simpa [e] using e.mk_first_second
  rcases Sym2.eq_iff.mp he with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · simpa [hfirst, hsecond] using hi
  · rw [hfirst, hsecond, ← hi]
    exact (F.matching i).apply_apply x

end OneFactorization

namespace SteinerTripleSystem

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (F : OneFactorization β α)

/-- The ordered triple attached to an edge in a Walecki factorization: its
factor index is the left vertex and the two edge endpoints are right vertices.
Every cross-edge appears in exactly one such triple once the full extension is
assembled. -/
noncomputable def waleckiCrossVertex (e : OffDiagonalPair β) : Fin 3 → α ⊕ β := fun i =>
  if i = 0 then Sum.inl (F.factorOfEdge e)
  else if i = 1 then Sum.inr e.first
  else Sum.inr e.second

@[simp] theorem waleckiCrossVertex_zero (e : OffDiagonalPair β) :
    waleckiCrossVertex F e 0 = Sum.inl (F.factorOfEdge e) := by
  simp [waleckiCrossVertex]

@[simp] theorem waleckiCrossVertex_one (e : OffDiagonalPair β) :
    waleckiCrossVertex F e 1 = Sum.inr e.first := by
  simp [waleckiCrossVertex]

@[simp] theorem waleckiCrossVertex_two (e : OffDiagonalPair β) :
    waleckiCrossVertex F e 2 = Sum.inr e.second := by
  simp [waleckiCrossVertex]

theorem waleckiCrossVertex_injective (e : OffDiagonalPair β) :
    Function.Injective (waleckiCrossVertex F e) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [waleckiCrossVertex] at hij ⊢
  · exact False.elim (e.first_ne_second hij)
  · exact False.elim (e.first_ne_second hij.symm)

theorem cross_left_factor {e : OffDiagonalPair β} {i : Fin 3} {a : α}
    (h : waleckiCrossVertex F e i = Sum.inl a) : F.factorOfEdge e = a := by
  fin_cases i <;> simp [waleckiCrossVertex] at h ⊢
  exact h

theorem cross_right_mem {e : OffDiagonalPair β} {i : Fin 3} {b : β}
    (h : waleckiCrossVertex F e i = Sum.inr b) : b ∈ e.1 := by
  fin_cases i
  · simp [waleckiCrossVertex] at h
  · have h' : e.first = b := Sum.inr.inj (α := α) (by simpa [waleckiCrossVertex] using h)
    rw [← h']
    exact e.1.out_fst_mem
  · have h' : e.second = b := Sum.inr.inj (α := α) (by simpa [waleckiCrossVertex] using h)
    rw [← h']
    exact e.1.out_snd_mem

theorem cross_contains_right (e : OffDiagonalPair β) (b : β) (hb : b ∈ e.1) :
    ∃ i : Fin 3, waleckiCrossVertex F e i = Sum.inr b := by
  rcases (e.mem_iff_first_or_second b).mp hb with h | h
  · refine ⟨1, ?_⟩
    simpa [waleckiCrossVertex, h]
  · refine ⟨2, ?_⟩
    simpa [waleckiCrossVertex, h]

/-- For each left point and right point, exactly one Walecki cross triple
contains both.  This is the key bridge from a one-factorization to the
standard `2a+1` Steiner-system extension. -/
theorem existsUnique_cross_of_left_right (a : α) (b : β) :
    ∃! e : OffDiagonalPair β,
      (∃ i : Fin 3, waleckiCrossVertex F e i = Sum.inl a) ∧
        ∃ j : Fin 3, waleckiCrossVertex F e j = Sum.inr b := by
  let c : β := (F.matching a).perm b
  have hbc : b ≠ c := (F.matching a).apply_ne b |>.symm
  let e₀ : OffDiagonalPair β := OffDiagonalPair.mk b c hbc
  have hfactor : F.factorOfEdge e₀ = a := by
    exact (F.factorOfEdge_mk_eq b c hbc a rfl).symm
  refine ⟨e₀, ?_, ?_⟩
  · constructor
    · refine ⟨0, ?_⟩
      rw [waleckiCrossVertex_zero, hfactor]
    · exact cross_contains_right F e₀ b (OffDiagonalPair.mem_mk_left b c hbc)
  · intro e he
    rcases he with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have hfactor' : F.factorOfEdge e = a := cross_left_factor F hi
    have hbmem : b ∈ e.1 := cross_right_mem F hj
    have hedge : e.1 = s(b, c) := by
      rcases (e.mem_iff_first_or_second b).mp hbmem with hfirst | hsecond
      · have hpartner : (F.matching a).perm e.first = e.second := by
          rw [← hfactor']
          exact F.matching_factorOfEdge_first e
        have hpartner' : e.second = c := by
          simpa [c, hfirst] using hpartner.symm
        calc
          e.1 = s(e.first, e.second) := e.mk_first_second.symm
          _ = s(b, c) := by rw [hfirst, hpartner']
      · have hpartner : (F.matching a).perm e.second = e.first := by
          rw [← hfactor']
          exact F.matching_factorOfEdge_second e
        have hpartner' : e.first = c := by
          simpa [c, hsecond] using hpartner.symm
        calc
          e.1 = s(e.first, e.second) := e.mk_first_second.symm
          _ = s(c, b) := by rw [hsecond, hpartner']
          _ = s(b, c) := Sym2.eq_swap
    apply Subtype.ext
    simpa [e₀] using hedge

/-- The triangle vertices in the Walecki extension.  Left triangles are the
input Steiner triples, while a right edge becomes its factor vertex together
with its two right endpoints. -/
noncomputable def waleckiExtensionVertex (S : SteinerTripleSystem α) :
    S.Triangle ⊕ OffDiagonalPair β → Fin 3 → α ⊕ β
  | Sum.inl t => fun i => Sum.inl (S.vertex t i)
  | Sum.inr e => waleckiCrossVertex F e

theorem waleckiExtensionVertex_injective (S : SteinerTripleSystem α)
    (t : S.Triangle ⊕ OffDiagonalPair β) :
    Function.Injective (waleckiExtensionVertex (F := F) S t) := by
  cases t with
  | inl t =>
      intro i j hij
      apply S.vertex_injective t
      exact Sum.inl.inj hij
  | inr e => exact waleckiCrossVertex_injective F e

private theorem waleckiExtension_pair_covered_once (S : SteinerTripleSystem α)
    (F : OneFactorization β α) : ∀ x y : α ⊕ β, x ≠ y →
      ∃! t : S.Triangle ⊕ OffDiagonalPair β,
        (∃ i : Fin 3, waleckiExtensionVertex (F := F) S t i = x) ∧
          ∃ j : Fin 3, waleckiExtensionVertex (F := F) S t j = y := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          have haa' : a ≠ a' := by
            intro h
            apply hxy
            simpa [h]
          let t₀ := S.triangleOfPair a a' haa'
          refine ⟨Sum.inl t₀, ?_, ?_⟩
          · rcases S.pair_mem_triangleOfPair a a' haa' with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            exact ⟨⟨i, congrArg Sum.inl hi⟩, ⟨j, congrArg Sum.inl hj⟩⟩
          · intro t ht
            rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            cases t with
            | inl t =>
                apply congrArg Sum.inl
                apply S.eq_triangleOfPair_of_contains a a' haa' t
                · refine ⟨i, ?_⟩
                  exact Sum.inl.inj hi
                · refine ⟨j, ?_⟩
                  exact Sum.inl.inj hj
            | inr e =>
                have hfactor : F.factorOfEdge e = a :=
                  cross_left_factor F hi
                have hfactor' : F.factorOfEdge e = a' :=
                  cross_left_factor F hj
                exact False.elim (haa' (hfactor.symm.trans hfactor'))
      | inr b =>
          rcases existsUnique_cross_of_left_right F a b with ⟨e, he, heuniq⟩
          refine ⟨Sum.inr e, he, ?_⟩
          intro t ht
          cases t with
          | inl t =>
              rcases ht.2 with ⟨j, hj⟩
              simp [waleckiExtensionVertex] at hj
          | inr e' =>
              apply congrArg Sum.inr
              exact heuniq e' ht
  | inr b =>
      cases y with
      | inl a =>
          rcases existsUnique_cross_of_left_right F a b with ⟨e, he, heuniq⟩
          refine ⟨Sum.inr e, ⟨he.2, he.1⟩, ?_⟩
          intro t ht
          cases t with
          | inl t =>
              rcases ht.1 with ⟨i, hi⟩
              simp [waleckiExtensionVertex] at hi
          | inr e' =>
              apply congrArg Sum.inr
              apply heuniq e'
              exact ⟨ht.2, ht.1⟩
      | inr b' =>
          have hbb' : b ≠ b' := by
            intro h
            apply hxy
            simpa [h]
          let e₀ : OffDiagonalPair β := OffDiagonalPair.mk b b' hbb'
          refine ⟨Sum.inr e₀, ?_, ?_⟩
          · exact ⟨cross_contains_right F e₀ b (OffDiagonalPair.mem_mk_left b b' hbb'),
              cross_contains_right F e₀ b' (OffDiagonalPair.mem_mk_right b b' hbb')⟩
          · intro t ht
            cases t with
            | inl t =>
                rcases ht.1 with ⟨i, hi⟩
                simp [waleckiExtensionVertex] at hi
            | inr e =>
                apply congrArg Sum.inr
                apply Subtype.ext
                apply (Sym2.mem_and_mem_iff hbb').mp
                constructor
                · exact cross_right_mem F ht.1.choose_spec
                · exact cross_right_mem F ht.2.choose_spec

/-- Walecki's extension construction (Feder--Subi Lemma 3): a Steiner triple
system on `α` together with a one-factorization of the complete graph on `β`
whose factors are indexed by `α` produces a Steiner triple system on
`α ⊕ β`. -/
noncomputable def waleckiExtension (S : SteinerTripleSystem α)
    (F : OneFactorization β α) : SteinerTripleSystem (α ⊕ β) where
  Triangle := S.Triangle ⊕ OffDiagonalPair β
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := waleckiExtensionVertex (F := F) S
  vertex_injective := waleckiExtensionVertex_injective (F := F) S
  pair_covered_once := waleckiExtension_pair_covered_once S F

section WaleckiSpecialization

variable {m : ℕ} [NeZero m]

/-- The concrete `2m+1` Walecki extension on the odd cyclic group `ZMod m`.
This is Feder--Subi Lemma 3 with the source's Walecki factorization supplied
by `Walecki.oneFactorization`. -/
noncomputable def waleckiDoublePlusOne (hm : Odd m)
    (S : SteinerTripleSystem (ZMod m)) :
    SteinerTripleSystem (ZMod m ⊕ Option (ZMod m)) :=
  waleckiExtension S (Walecki.oneFactorization hm)

private theorem card_waleckiDoublePlusOneCarrier :
    Fintype.card (ZMod m ⊕ Option (ZMod m)) = 2 * m + 1 := by
  rw [Fintype.card_sum, Fintype.card_option, ZMod.card]
  omega

/-- A finite-indexed form of the Walecki extension. -/
noncomputable def waleckiDoublePlusOneFin (hm : Odd m)
    (S : SteinerTripleSystem (ZMod m)) : SteinerTripleSystem (Fin (2 * m + 1)) :=
  SteinerTripleSystem.map
    (Fintype.equivFinOfCardEq card_waleckiDoublePlusOneCarrier)
    (waleckiDoublePlusOne hm S)

/-- Feder--Subi Lemma 3 in the paper's finite-label convention: a triple
system on `m` points, with `m` odd, constructively yields one on `2m+1`
points. -/
noncomputable def waleckiDoublePlusOneFinOfFin (hm : Odd m)
    (S : SteinerTripleSystem (Fin m)) : SteinerTripleSystem (Fin (2 * m + 1)) :=
  let relabel : ZMod m ≃ Fin m := Fintype.equivFinOfCardEq (ZMod.card m)
  waleckiDoublePlusOneFin hm (SteinerTripleSystem.map relabel.symm S)

end WaleckiSpecialization

section TriplingSpecialization

variable {m : ℕ} [NeZero m]

/-- The transversal triple in Feder--Subi Lemma 4.  The pair `(x,y)` indexes
the three vertices `(0,x)`, `(1,y)`, and `(2,x+y)` in the three copies of the
cyclic group. -/
noncomputable def triplingCrossVertex (p : ZMod m × ZMod m) : Fin 3 → Fin 3 × ZMod m := fun i =>
  if i = 0 then (0, p.1)
  else if i = 1 then (1, p.2)
  else (2, p.1 + p.2)

@[simp] theorem triplingCrossVertex_zero (p : ZMod m × ZMod m) :
    triplingCrossVertex p 0 = (0, p.1) := by
  simp [triplingCrossVertex]

@[simp] theorem triplingCrossVertex_one (p : ZMod m × ZMod m) :
    triplingCrossVertex p 1 = (1, p.2) := by
  simp [triplingCrossVertex]

@[simp] theorem triplingCrossVertex_two (p : ZMod m × ZMod m) :
    triplingCrossVertex p 2 = (2, p.1 + p.2) := by
  simp [triplingCrossVertex]

theorem triplingCrossVertex_injective (p : ZMod m × ZMod m) :
    Function.Injective (triplingCrossVertex p) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [triplingCrossVertex] at hij ⊢

/-- The fibre number of a vertex in a transversal triple is its displayed
index. -/
theorem triplingCrossVertex_index_eq_fst {p : ZMod m × ZMod m}
    {i a : Fin 3} {x : ZMod m}
    (h : triplingCrossVertex p i = (a, x)) : i = a := by
  fin_cases i <;> fin_cases a <;> simp [triplingCrossVertex] at h ⊢

private theorem tripling_cross_fst_of_eq_zero {p : ZMod m × ZMod m}
    {i : Fin 3} {x : ZMod m}
    (h : triplingCrossVertex p i = (0, x)) : p.1 = x := by
  fin_cases i
  · simpa [triplingCrossVertex] using congrArg Prod.snd h
  · simp [triplingCrossVertex] at h
  · simp [triplingCrossVertex] at h

private theorem tripling_cross_snd_of_eq_one {p : ZMod m × ZMod m}
    {i : Fin 3} {x : ZMod m}
    (h : triplingCrossVertex p i = (1, x)) : p.2 = x := by
  fin_cases i
  · simp [triplingCrossVertex] at h
  · simpa [triplingCrossVertex] using congrArg Prod.snd h
  · simp [triplingCrossVertex] at h

private theorem tripling_cross_sum_of_eq_two {p : ZMod m × ZMod m}
    {i : Fin 3} {x : ZMod m}
    (h : triplingCrossVertex p i = (2, x)) : p.1 + p.2 = x := by
  fin_cases i
  · simp [triplingCrossVertex] at h
  · simp [triplingCrossVertex] at h
  · simpa [triplingCrossVertex] using congrArg Prod.snd h

private theorem existsUnique_triplingCross_zero_one (x y : ZMod m) :
    ∃! p : ZMod m × ZMod m,
      (∃ i : Fin 3, triplingCrossVertex p i = (0, x)) ∧
        ∃ j : Fin 3, triplingCrossVertex p j = (1, y) := by
  refine ⟨(x, y), ⟨⟨0, triplingCrossVertex_zero _⟩,
    ⟨1, triplingCrossVertex_one _⟩⟩, ?_⟩
  intro p hp
  rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  exact Prod.ext (tripling_cross_fst_of_eq_zero hi) (tripling_cross_snd_of_eq_one hj)

private theorem existsUnique_triplingCross_one_zero (x y : ZMod m) :
    ∃! p : ZMod m × ZMod m,
      (∃ i : Fin 3, triplingCrossVertex p i = (1, x)) ∧
        ∃ j : Fin 3, triplingCrossVertex p j = (0, y) := by
  refine ⟨(y, x), ⟨⟨1, triplingCrossVertex_one _⟩,
    ⟨0, triplingCrossVertex_zero _⟩⟩, ?_⟩
  intro p hp
  rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  exact Prod.ext (tripling_cross_fst_of_eq_zero hj) (tripling_cross_snd_of_eq_one hi)

private theorem existsUnique_triplingCross_zero_two (x y : ZMod m) :
    ∃! p : ZMod m × ZMod m,
      (∃ i : Fin 3, triplingCrossVertex p i = (0, x)) ∧
        ∃ j : Fin 3, triplingCrossVertex p j = (2, y) := by
  refine ⟨(x, y - x), ⟨⟨0, triplingCrossVertex_zero _⟩,
    ⟨2, by simp [triplingCrossVertex]⟩⟩, ?_⟩
  intro p hp
  rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  apply Prod.ext
  · exact tripling_cross_fst_of_eq_zero hi
  · have hfst := tripling_cross_fst_of_eq_zero hi
    have hsum := tripling_cross_sum_of_eq_two hj
    calc
      p.2 = (p.1 + p.2) - p.1 := by abel
      _ = y - x := by rw [hsum, hfst]

private theorem existsUnique_triplingCross_two_zero (x y : ZMod m) :
    ∃! p : ZMod m × ZMod m,
      (∃ i : Fin 3, triplingCrossVertex p i = (2, x)) ∧
        ∃ j : Fin 3, triplingCrossVertex p j = (0, y) := by
  refine ⟨(y, x - y), ⟨⟨2, by simp [triplingCrossVertex]⟩,
    ⟨0, triplingCrossVertex_zero _⟩⟩, ?_⟩
  intro p hp
  rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  apply Prod.ext
  · exact tripling_cross_fst_of_eq_zero hj
  · have hfst := tripling_cross_fst_of_eq_zero hj
    have hsum := tripling_cross_sum_of_eq_two hi
    calc
      p.2 = (p.1 + p.2) - p.1 := by abel
      _ = x - y := by rw [hsum, hfst]

private theorem existsUnique_triplingCross_one_two (x y : ZMod m) :
    ∃! p : ZMod m × ZMod m,
      (∃ i : Fin 3, triplingCrossVertex p i = (1, x)) ∧
        ∃ j : Fin 3, triplingCrossVertex p j = (2, y) := by
  refine ⟨(y - x, x), ⟨⟨1, triplingCrossVertex_one _⟩,
    ⟨2, by simp [triplingCrossVertex]⟩⟩, ?_⟩
  intro p hp
  rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  apply Prod.ext
  · have hsnd := tripling_cross_snd_of_eq_one hi
    have hsum := tripling_cross_sum_of_eq_two hj
    calc
      p.1 = (p.1 + p.2) - p.2 := by abel
      _ = y - x := by rw [hsum, hsnd]
  · exact tripling_cross_snd_of_eq_one hi

private theorem existsUnique_triplingCross_two_one (x y : ZMod m) :
    ∃! p : ZMod m × ZMod m,
      (∃ i : Fin 3, triplingCrossVertex p i = (2, x)) ∧
        ∃ j : Fin 3, triplingCrossVertex p j = (1, y) := by
  refine ⟨(x - y, y), ⟨⟨2, by simp [triplingCrossVertex]⟩,
    ⟨1, triplingCrossVertex_one _⟩⟩, ?_⟩
  intro p hp
  rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  apply Prod.ext
  · have hsnd := tripling_cross_snd_of_eq_one hj
    have hsum := tripling_cross_sum_of_eq_two hi
    calc
      p.1 = (p.1 + p.2) - p.2 := by abel
      _ = x - y := by rw [hsum, hsnd]
  · exact tripling_cross_snd_of_eq_one hj

/-- Every pair of points in distinct fibres occurs in a unique transversal
triple from the cyclic construction. -/
theorem existsUnique_triplingCross_of_distinct (a b : Fin 3)
    (x y : ZMod m) (hab : a ≠ b) :
    ∃! p : ZMod m × ZMod m,
      (∃ i : Fin 3, triplingCrossVertex p i = (a, x)) ∧
        ∃ j : Fin 3, triplingCrossVertex p j = (b, y) := by
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · exact existsUnique_triplingCross_zero_one x y
  · exact existsUnique_triplingCross_zero_two x y
  · exact existsUnique_triplingCross_one_zero x y
  · exact False.elim (hab rfl)
  · exact existsUnique_triplingCross_one_two x y
  · exact existsUnique_triplingCross_two_zero x y
  · exact existsUnique_triplingCross_two_one x y
  · exact False.elim (hab rfl)

/-- The triangle vertices in the tripling construction: each input triangle is
copied into one fibre, and a pair of cyclic indices gives one transversal
triangle. -/
noncomputable def triplingVertex (S : SteinerTripleSystem (ZMod m)) :
    (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m) → Fin 3 → Fin 3 × ZMod m
  | Sum.inl (a, t) => fun i => (a, S.vertex t i)
  | Sum.inr p => triplingCrossVertex p

theorem triplingVertex_injective (S : SteinerTripleSystem (ZMod m))
    (t : (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m)) :
    Function.Injective (triplingVertex S t) := by
  cases t with
  | inl q =>
      rcases q with ⟨a, t⟩
      intro i j hij
      apply S.vertex_injective t
      exact congrArg Prod.snd hij
  | inr p => exact triplingCrossVertex_injective p

private theorem tripling_pair_covered_once (S : SteinerTripleSystem (ZMod m)) :
    ∀ x y : Fin 3 × ZMod m, x ≠ y →
      ∃! t : (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m),
        (∃ i : Fin 3, triplingVertex S t i = x) ∧
          ∃ j : Fin 3, triplingVertex S t j = y := by
  rintro ⟨a, x⟩ ⟨b, y⟩ hxy
  by_cases hab : a = b
  · subst b
    have hxy' : x ≠ y := by
      intro h
      apply hxy
      simp [h]
    let t₀ := S.triangleOfPair x y hxy'
    refine ⟨Sum.inl (a, t₀), ?_, ?_⟩
    · rcases S.pair_mem_triangleOfPair x y hxy' with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨⟨i, Prod.ext rfl hi⟩, ⟨j, Prod.ext rfl hj⟩⟩
    · intro t ht
      rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      cases t with
      | inl q =>
          rcases q with ⟨c, t⟩
          have hca : c = a := congrArg Prod.fst hi
          apply congrArg Sum.inl
          subst c
          apply congrArg (fun u => (a, u))
          apply S.eq_triangleOfPair_of_contains x y hxy' t
          · exact ⟨i, congrArg Prod.snd hi⟩
          · exact ⟨j, congrArg Prod.snd hj⟩
      | inr p =>
          have hia : i = a := triplingCrossVertex_index_eq_fst hi
          have hja : j = a := triplingCrossVertex_index_eq_fst hj
          have hij : i = j := hia.trans hja.symm
          exact False.elim (hxy' (congrArg Prod.snd (by
            calc
              (a, x) = triplingCrossVertex p i := hi.symm
              _ = triplingCrossVertex p j := by rw [hij]
              _ = (a, y) := hj)))
  · rcases existsUnique_triplingCross_of_distinct a b x y hab with ⟨p, hp, hpuniq⟩
    refine ⟨Sum.inr p, hp, ?_⟩
    intro t ht
    cases t with
    | inl q =>
        rcases q with ⟨c, t⟩
        rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        have hca : c = a := congrArg Prod.fst hi
        have hcb : c = b := congrArg Prod.fst hj
        exact False.elim (hab (hca.symm.trans hcb))
    | inr p' =>
        apply congrArg Sum.inr
        exact hpuniq p' ht

/-- Feder--Subi Lemma 4: copying a cyclic Steiner triple system into three
fibres and adding the displayed transversal triples yields a system on three
times as many points. -/
noncomputable def tripling (S : SteinerTripleSystem (ZMod m)) :
    SteinerTripleSystem (Fin 3 × ZMod m) where
  Triangle := (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m)
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := triplingVertex S
  vertex_injective := triplingVertex_injective S
  pair_covered_once := tripling_pair_covered_once S

private theorem card_triplingCarrier : Fintype.card (Fin 3 × ZMod m) = 3 * m := by
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]

/-- Feder--Subi Lemma 4 with finite labels: `STS(m) -> STS(3m)`. -/
noncomputable def triplingFinOfFin (S : SteinerTripleSystem (Fin m)) :
    SteinerTripleSystem (Fin (3 * m)) :=
  let relabel : ZMod m ≃ Fin m := Fintype.equivFinOfCardEq (ZMod.card m)
  SteinerTripleSystem.map
    (Fintype.equivFinOfCardEq card_triplingCarrier)
    (tripling (SteinerTripleSystem.map relabel.symm S))

end TriplingSpecialization

section CenteredTriplingSpecialization

variable {m : ℕ} [NeZero m]

/-- The carrier of the shared-center version of the tripling construction.
The one `PUnit` point is used by all three copies of the input system. -/
abbrev centeredTriplingCarrier (m : ℕ) := (Fin 3 × ZMod m) ⊕ PUnit

noncomputable def centeredCopyVertex (a : Fin 3) :
    Option (ZMod m) → centeredTriplingCarrier m
  | none => Sum.inr PUnit.unit
  | some x => Sum.inl (a, x)

private theorem centeredCopyVertex_injective (a : Fin 3) :
    Function.Injective (centeredCopyVertex (m := m) a) := by
  intro x y h
  cases x <;> cases y <;> simp [centeredCopyVertex] at h ⊢
  exact h

private theorem centeredCopyVertex_eq_copy {a c : Fin 3} {x : ZMod m}
    {z : Option (ZMod m)}
    (h : centeredCopyVertex (m := m) c z = Sum.inl (a, x)) : c = a ∧ z = some x := by
  cases z with
  | none => simp [centeredCopyVertex] at h
  | some z =>
      have h' : (c, z) = (a, x) := by simpa [centeredCopyVertex] using h
      exact ⟨congrArg Prod.fst h', congrArg some (congrArg Prod.snd h')⟩

private theorem centeredCopyVertex_eq_center {a : Fin 3} {z : Option (ZMod m)}
    (h : centeredCopyVertex (m := m) a z = Sum.inr PUnit.unit) : z = none := by
  cases z <;> simp [centeredCopyVertex] at h ⊢

noncomputable def centeredTriplingCrossVertex (p : ZMod m × ZMod m) :
    Fin 3 → centeredTriplingCarrier m := fun i => Sum.inl (triplingCrossVertex p i)

private theorem centeredTriplingCrossVertex_injective (p : ZMod m × ZMod m) :
    Function.Injective (centeredTriplingCrossVertex p) := by
  intro i j hij
  apply triplingCrossVertex_injective p
  exact Sum.inl.inj hij

/-- The triangle vertices for Feder--Subi Lemma 5.  Each copy of the input
system shares its `none` point with the other two copies. -/
noncomputable def centeredTriplingVertex (S : SteinerTripleSystem (Option (ZMod m))) :
    (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m) → Fin 3 → centeredTriplingCarrier m
  | Sum.inl (a, t) => fun i => centeredCopyVertex a (S.vertex t i)
  | Sum.inr p => centeredTriplingCrossVertex p

private theorem centeredTriplingVertex_injective (S : SteinerTripleSystem (Option (ZMod m)))
    (t : (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m)) :
    Function.Injective (centeredTriplingVertex S t) := by
  cases t with
  | inl q =>
      rcases q with ⟨a, t⟩
      exact (centeredCopyVertex_injective a).comp (S.vertex_injective t)
  | inr p => exact centeredTriplingCrossVertex_injective p

private theorem centeredTripling_pair_covered_once (S : SteinerTripleSystem (Option (ZMod m))) :
    ∀ x y : centeredTriplingCarrier m, x ≠ y →
      ∃! t : (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m),
        (∃ i : Fin 3, centeredTriplingVertex S t i = x) ∧
          ∃ j : Fin 3, centeredTriplingVertex S t j = y := by
  intro x y hxy
  cases x with
  | inl ax =>
      rcases ax with ⟨a, x⟩
      cases y with
      | inl by_ =>
          rcases by_ with ⟨b, y⟩
          by_cases hab : a = b
          · subst b
            have hxy' : x ≠ y := by
              intro h
              apply hxy
              simp [h]
            have hsxy : (some x : Option (ZMod m)) ≠ some y := by simpa using hxy'
            let t₀ := S.triangleOfPair (some x) (some y) hsxy
            refine ⟨Sum.inl (a, t₀), ?_, ?_⟩
            · rcases S.pair_mem_triangleOfPair (some x) (some y) hsxy with
                ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
              exact ⟨⟨i, by
                simpa [t₀, centeredCopyVertex] using congrArg (centeredCopyVertex a) hi⟩,
                ⟨j, by
                  simpa [t₀, centeredCopyVertex] using congrArg (centeredCopyVertex a) hj⟩⟩
            · intro t ht
              rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
              cases t with
              | inl q =>
                  rcases q with ⟨c, t⟩
                  rcases centeredCopyVertex_eq_copy (m := m) hi with ⟨hca, hvi⟩
                  rcases centeredCopyVertex_eq_copy (m := m) hj with ⟨_, hvj⟩
                  apply congrArg Sum.inl
                  subst c
                  apply congrArg (fun u => (a, u))
                  apply S.eq_triangleOfPair_of_contains (some x) (some y) hsxy t
                  · exact ⟨i, hvi⟩
                  · exact ⟨j, hvj⟩
              | inr p =>
                  have hia : i = a := triplingCrossVertex_index_eq_fst (Sum.inl.inj hi)
                  have hja : j = a := triplingCrossVertex_index_eq_fst (Sum.inl.inj hj)
                  have hij : i = j := hia.trans hja.symm
                  exact False.elim (hxy' (congrArg Prod.snd (by
                    calc
                      (a, x) = triplingCrossVertex p i := Sum.inl.inj hi.symm
                      _ = triplingCrossVertex p j := by rw [hij]
                      _ = (a, y) := Sum.inl.inj hj)))
          · rcases existsUnique_triplingCross_of_distinct a b x y hab with ⟨p, hp, hpuniq⟩
            refine ⟨Sum.inr p, ?_, ?_⟩
            · rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
              exact ⟨⟨i, congrArg Sum.inl hi⟩, ⟨j, congrArg Sum.inl hj⟩⟩
            intro t ht
            cases t with
            | inl q =>
                rcases q with ⟨c, t⟩
                rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
                have hca := (centeredCopyVertex_eq_copy (m := m) hi).1
                have hcb := (centeredCopyVertex_eq_copy (m := m) hj).1
                exact False.elim (hab (hca.symm.trans hcb))
            | inr p' =>
                apply congrArg Sum.inr
                apply hpuniq p'
                rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
                exact ⟨⟨i, Sum.inl.inj hi⟩, ⟨j, Sum.inl.inj hj⟩⟩
      | inr u =>
          cases u
          have hsx : (some x : Option (ZMod m)) ≠ none := by simp
          let t₀ := S.triangleOfPair (some x) none hsx
          refine ⟨Sum.inl (a, t₀), ?_, ?_⟩
          · rcases S.pair_mem_triangleOfPair (some x) none hsx with
              ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            exact ⟨⟨i, by
              simpa [t₀, centeredCopyVertex] using congrArg (centeredCopyVertex a) hi⟩,
              ⟨j, by
                simpa [t₀, centeredCopyVertex] using congrArg (centeredCopyVertex a) hj⟩⟩
          · intro t ht
            rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            cases t with
            | inl q =>
                rcases q with ⟨c, t⟩
                rcases centeredCopyVertex_eq_copy (m := m) hi with ⟨hca, hvi⟩
                have hnone := centeredCopyVertex_eq_center (m := m) hj
                apply congrArg Sum.inl
                subst c
                apply congrArg (fun u => (a, u))
                apply S.eq_triangleOfPair_of_contains (some x) none hsx t
                · exact ⟨i, hvi⟩
                · exact ⟨j, hnone⟩
            | inr p =>
                simp [centeredTriplingVertex, centeredTriplingCrossVertex] at hj
  | inr u =>
      cases u
      cases y with
      | inl ax =>
          rcases ax with ⟨a, x⟩
          have hsx : (none : Option (ZMod m)) ≠ some x := by simp
          let t₀ := S.triangleOfPair none (some x) hsx
          refine ⟨Sum.inl (a, t₀), ?_, ?_⟩
          · rcases S.pair_mem_triangleOfPair none (some x) hsx with
              ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            exact ⟨⟨i, by
              simpa [t₀, centeredCopyVertex] using congrArg (centeredCopyVertex a) hi⟩,
              ⟨j, by
                simpa [t₀, centeredCopyVertex] using congrArg (centeredCopyVertex a) hj⟩⟩
          · intro t ht
            rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            cases t with
            | inl q =>
                rcases q with ⟨c, t⟩
                have hnone := centeredCopyVertex_eq_center (m := m) hi
                rcases centeredCopyVertex_eq_copy (m := m) hj with ⟨hca, hvj⟩
                apply congrArg Sum.inl
                subst c
                apply congrArg (fun u => (a, u))
                apply S.eq_triangleOfPair_of_contains none (some x) hsx t
                · exact ⟨i, hnone⟩
                · exact ⟨j, hvj⟩
            | inr p =>
                simp [centeredTriplingVertex, centeredTriplingCrossVertex] at hi
      | inr u' =>
          cases u'
          exact False.elim (hxy rfl)

/-- Feder--Subi Lemma 5: `STS(c)` gives `STS(3c-2)` after three copies share
one distinguished point and receive the transversal cyclic triples. -/
noncomputable def centeredTripling (S : SteinerTripleSystem (Option (ZMod m))) :
    SteinerTripleSystem (centeredTriplingCarrier m) where
  Triangle := (Fin 3 × S.Triangle) ⊕ (ZMod m × ZMod m)
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := centeredTriplingVertex S
  vertex_injective := centeredTriplingVertex_injective S
  pair_covered_once := centeredTripling_pair_covered_once S

private theorem card_centeredTriplingCarrier :
    Fintype.card (centeredTriplingCarrier m) = 3 * (m + 1) - 2 := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card, Fintype.card_punit]
  omega

/-- Feder--Subi Lemma 5 in finite labels, for the nontrivial sizes used by
the recursive Kirkman construction: `STS(m+1) -> STS(3(m+1)-2)`. -/
noncomputable def centeredTriplingFinOfFin (S : SteinerTripleSystem (Fin (m + 1))) :
    SteinerTripleSystem (Fin (3 * (m + 1) - 2)) :=
  let relabel : Option (ZMod m) ≃ Fin (m + 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_option, ZMod.card])
  SteinerTripleSystem.map
    (Fintype.equivFinOfCardEq card_centeredTriplingCarrier)
    (centeredTripling (SteinerTripleSystem.map relabel.symm S))

end CenteredTriplingSpecialization

section ThirteenPointBase

private def addModThirteen (x : Fin 13) (k : ℕ) : Fin 13 :=
  ⟨(x.1 + k) % 13, Nat.mod_lt _ (by decide)⟩

/-- The two cyclic base blocks `{0,1,4}` and `{0,5,11}`, translated through
`Fin 13`. Their nonzero differences partition the twelve nonzero residues,
so their 26 translates form an explicit Steiner triple system. -/
private def finThirteenVertex : Bool × Fin 13 → Fin 3 → Fin 13
  | (false, t), i =>
      if i = 0 then addModThirteen t 0
      else if i = 1 then addModThirteen t 1
      else addModThirteen t 4
  | (true, t), i =>
      if i = 0 then addModThirteen t 0
      else if i = 1 then addModThirteen t 5
      else addModThirteen t 11

/-- A concrete 13-point Steiner triple system. The source uses a different
displayed list for Feder--Subi Lemma 6; this cyclic presentation proves the
same finite base claim by a complete check of its 26 displayed translates. -/
def finThirteen : SteinerTripleSystem (Fin 13) where
  Triangle := Bool × Fin 13
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := finThirteenVertex
  vertex_injective := by decide
  pair_covered_once := by
    intro x y hxy
    by_cases hEq : x = y
    · exact False.elim (hxy hEq)
    · let P : Bool × Fin 13 → Prop := fun t =>
        (∃ i : Fin 3, finThirteenVertex t i = x) ∧
          ∃ j : Fin 3, finThirteenVertex t j = y
      letI : DecidablePred P := fun _ => inferInstance
      letI : Decidable (∃! t, P t) := by
        change Decidable (∃ t, P t ∧ ∀ u, P u → u = t)
        infer_instance
      change ∃! t, P t
      fin_cases x <;> fin_cases y
      all_goals (first | contradiction | decide)

end ThirteenPointBase

section SixTimesMinusFive

/-- The distinguished super-vertex in the 13-point base used by
Feder--Subi Lemma 7. -/
private abbrev finThirteenCenter : Fin 13 := 0

/-- A line of the 13-point base passing through its distinguished point. -/
private abbrev finThirteenCenterLine :=
  {t : finThirteen.Triangle // ∃ i : Fin 3, finThirteen.vertex t i = finThirteenCenter}

/-- The two noncentral positions on a line through the distinguished point. -/
private abbrev finThirteenSideIndex (t : finThirteenCenterLine) :=
  {i : Fin 3 // finThirteen.vertex t.1 i ≠ finThirteenCenter}

private theorem card_finThirteenSideIndex (t : finThirteenCenterLine) :
    Fintype.card (finThirteenSideIndex t) = 2 := by
  classical
  let k : Fin 3 := t.2.choose
  have hk : finThirteen.vertex t.1 k = finThirteenCenter := t.2.choose_spec
  letI : Unique {i : Fin 3 // finThirteen.vertex t.1 i = finThirteenCenter} :=
    { default := ⟨k, hk⟩
      uniq := by
        intro i
        apply Subtype.ext
        apply finThirteen.vertex_injective t.1
        exact i.2.trans hk.symm }
  have hcard_center :
      Fintype.card {i : Fin 3 // finThirteen.vertex t.1 i = finThirteenCenter} = 1 :=
    Fintype.card_unique
  have hcompl := Fintype.card_subtype_compl
    (fun i : Fin 3 => finThirteen.vertex t.1 i = finThirteenCenter)
  rw [hcard_center] at hcompl
  simpa only [Fintype.card_fin, Nat.reduceSub] using hcompl

private noncomputable def finThirteenSideEquiv (t : finThirteenCenterLine) :
    Fin 2 ≃ finThirteenSideIndex t :=
  (Fintype.equivFinOfCardEq (card_finThirteenSideIndex t)).symm

private noncomputable def finThirteenSideVertex (t : finThirteenCenterLine) :
    Fin 2 → {a : Fin 13 // a ≠ finThirteenCenter} := fun i =>
  ⟨finThirteen.vertex t.1 (finThirteenSideEquiv t i).1, (finThirteenSideEquiv t i).2⟩

private theorem finThirteenSideVertex_injective (t : finThirteenCenterLine) :
    Function.Injective (finThirteenSideVertex t) := by
  intro i j hij
  apply (finThirteenSideEquiv t).injective
  apply Subtype.ext
  apply finThirteen.vertex_injective t.1
  exact congrArg Subtype.val hij

private noncomputable def finThirteenCenterLineOf
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) : finThirteenCenterLine :=
  ⟨finThirteen.triangleOfPair finThirteenCenter a.1 (fun h => a.2 h.symm),
    (finThirteen.pair_mem_triangleOfPair finThirteenCenter a.1
      (fun h => a.2 h.symm)).1⟩

private theorem finThirteenCenterLineOf_eq_of_vertex
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) (t : finThirteenCenterLine)
    (ha : ∃ i : Fin 3, finThirteen.vertex t.1 i = a.1) :
    finThirteenCenterLineOf a = t := by
  apply Subtype.ext
  exact (finThirteen.eq_triangleOfPair_of_contains finThirteenCenter a.1
    (fun h => a.2 h.symm) t.1 t.2 ha).symm

private noncomputable def finThirteenSideOf
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) :
    finThirteenSideIndex (finThirteenCenterLineOf a) :=
  ⟨(finThirteen.pair_mem_triangleOfPair finThirteenCenter a.1
      (fun h => a.2 h.symm)).2.choose,
    by
      intro h
      apply a.2
      exact (finThirteen.pair_mem_triangleOfPair finThirteenCenter a.1
        (fun h => a.2 h.symm)).2.choose_spec.symm.trans h⟩

private noncomputable def finThirteenSideNumber
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) : Fin 2 :=
  (finThirteenSideEquiv (finThirteenCenterLineOf a)).symm (finThirteenSideOf a)

private theorem finThirteenSideVertex_number
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) :
    finThirteenSideVertex (finThirteenCenterLineOf a) (finThirteenSideNumber a) = a := by
  apply Subtype.ext
  have hindex :
      finThirteenSideEquiv (finThirteenCenterLineOf a) (finThirteenSideNumber a) =
        finThirteenSideOf a :=
    (finThirteenSideEquiv (finThirteenCenterLineOf a)).apply_symm_apply _
  change finThirteen.vertex (finThirteen.triangleOfPair finThirteenCenter a.1
    (fun h => a.2 h.symm))
      ((finThirteenSideEquiv (finThirteenCenterLineOf a)
        (finThirteenSideNumber a)).1) = a.1
  rw [hindex]
  exact (finThirteen.pair_mem_triangleOfPair finThirteenCenter a.1
    (fun h => a.2 h.symm)).2.choose_spec

/-- The noncentral super-vertices of the base system, expanded to groups of
size `g`; the right summand is the shared center. -/
private abbrev sixTimesMinusFiveCarrier (g : ℕ) :=
  ({a : Fin 13 // a ≠ finThirteenCenter} × ZMod g) ⊕ PUnit.{1}

private abbrev finThirteenPeripheralTriangle :=
  {t : finThirteen.Triangle // ∀ i : Fin 3, finThirteen.vertex t i ≠ finThirteenCenter}

variable {g : ℕ} [NeZero g]

private noncomputable def sixTimesMinusFiveInternalVertex (t : finThirteenCenterLine) :
    Option (Fin 2 × ZMod g) → sixTimesMinusFiveCarrier g
  | none => Sum.inr PUnit.unit
  | some (i, x) => Sum.inl (finThirteenSideVertex t i, x)

private theorem sixTimesMinusFiveInternalVertex_injective (t : finThirteenCenterLine) :
    Function.Injective (sixTimesMinusFiveInternalVertex (g := g) t) := by
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y => simp [sixTimesMinusFiveInternalVertex] at hxy
  | some x =>
      rcases x with ⟨i, x⟩
      cases y with
      | none => simp [sixTimesMinusFiveInternalVertex] at hxy
      | some y =>
          rcases y with ⟨j, y⟩
          have hsum :
              (Sum.inl (finThirteenSideVertex t i, x) : sixTimesMinusFiveCarrier g) =
                (Sum.inl (finThirteenSideVertex t j, y) : sixTimesMinusFiveCarrier g) := by
            simpa [sixTimesMinusFiveInternalVertex] using hxy
          have h : (finThirteenSideVertex t i, x) = (finThirteenSideVertex t j, y) :=
            Sum.inl.inj hsum
          have hij : i = j := finThirteenSideVertex_injective t (congrArg Prod.fst h)
          have hxy' : x = y :=
            congrArg (fun q : {a : Fin 13 // a ≠ finThirteenCenter} × ZMod g => q.2) h
          exact congrArg some (Prod.ext hij hxy')

private theorem sixTimesMinusFiveInternalVertex_eq_center
    (t : finThirteenCenterLine) (x : Option (Fin 2 × ZMod g))
    (h : sixTimesMinusFiveInternalVertex (g := g) t x = Sum.inr PUnit.unit) : x = none := by
  cases x <;> simp [sixTimesMinusFiveInternalVertex] at h ⊢

private theorem sixTimesMinusFiveInternalVertex_eq_atom
    (t : finThirteenCenterLine) (x : Option (Fin 2 × ZMod g))
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) (z : ZMod g)
    (h : sixTimesMinusFiveInternalVertex (g := g) t x = Sum.inl (a, z)) :
    ∃ k : Fin 2, x = some (k, z) ∧ finThirteenSideVertex t k = a := by
  cases x with
  | none => simp [sixTimesMinusFiveInternalVertex] at h
  | some x =>
      rcases x with ⟨k, w⟩
      have hsum :
          (Sum.inl (finThirteenSideVertex t k, w) : sixTimesMinusFiveCarrier g) =
            (Sum.inl (a, z) : sixTimesMinusFiveCarrier g) := by
        simpa [sixTimesMinusFiveInternalVertex] using h
      have h' : (finThirteenSideVertex t k, w) = (a, z) := Sum.inl.inj hsum
      exact ⟨k, by simpa using congrArg Prod.snd h', congrArg Prod.fst h'⟩

private theorem finThirteenCenterLineOf_eq_of_sideVertex
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) (t : finThirteenCenterLine)
    (k : Fin 2) (h : finThirteenSideVertex t k = a) :
    finThirteenCenterLineOf a = t :=
  finThirteenCenterLineOf_eq_of_vertex a t
    ⟨(finThirteenSideEquiv t k).1, congrArg Subtype.val h⟩

private noncomputable def sixTimesMinusFiveExternalVertex
    (t : finThirteenPeripheralTriangle) (p : ZMod g × ZMod g) :
    Fin 3 → sixTimesMinusFiveCarrier g := fun i =>
  Sum.inl (⟨finThirteen.vertex t.1 i, t.2 i⟩, (triplingCrossVertex p i).2)

private theorem sixTimesMinusFiveExternalVertex_injective
    (t : finThirteenPeripheralTriangle) (p : ZMod g × ZMod g) :
    Function.Injective (sixTimesMinusFiveExternalVertex (g := g) t p) := by
  intro i j hij
  apply finThirteen.vertex_injective t.1
  have hsum :
      (Sum.inl (⟨finThirteen.vertex t.1 i, t.2 i⟩,
        (triplingCrossVertex p i).2) : sixTimesMinusFiveCarrier g) =
        (Sum.inl (⟨finThirteen.vertex t.1 j, t.2 j⟩,
          (triplingCrossVertex p j).2) : sixTimesMinusFiveCarrier g) := hij
  have h' :
      ((⟨finThirteen.vertex t.1 i, t.2 i⟩ :
          {a : Fin 13 // a ≠ finThirteenCenter}), (triplingCrossVertex p i).2) =
        ((⟨finThirteen.vertex t.1 j, t.2 j⟩ :
          {a : Fin 13 // a ≠ finThirteenCenter}), (triplingCrossVertex p j).2) :=
    Sum.inl.inj hsum
  exact congrArg (fun q : {a : Fin 13 // a ≠ finThirteenCenter} × ZMod g => q.1.1) h'

private theorem sixTimesMinusFiveExternalVertex_eq_atom
    (t : finThirteenPeripheralTriangle) (p : ZMod g × ZMod g) (i : Fin 3)
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) (z : ZMod g)
    (h : sixTimesMinusFiveExternalVertex (g := g) t p i = Sum.inl (a, z)) :
    finThirteen.vertex t.1 i = a.1 ∧ (triplingCrossVertex p i).2 = z := by
  have h' :
      (⟨finThirteen.vertex t.1 i, t.2 i⟩, (triplingCrossVertex p i).2) = (a, z) :=
    Sum.inl.inj (show
      (Sum.inl (⟨finThirteen.vertex t.1 i, t.2 i⟩,
        (triplingCrossVertex p i).2) : sixTimesMinusFiveCarrier g) =
          (Sum.inl (a, z) : sixTimesMinusFiveCarrier g) from h)
  exact ⟨congrArg (fun q : {a : Fin 13 // a ≠ finThirteenCenter} × ZMod g => q.1.1) h',
    congrArg Prod.snd h'⟩

private theorem finThirteen_triangleOfPair_peripheral_of_distinct_lines
    (a b : {a : Fin 13 // a ≠ finThirteenCenter})
    (hline : finThirteenCenterLineOf a ≠ finThirteenCenterLineOf b) :
    ∀ i : Fin 3,
      finThirteen.vertex (finThirteen.triangleOfPair a.1 b.1 (by
        intro h
        apply hline
        exact congrArg finThirteenCenterLineOf (Subtype.ext h))) i ≠ finThirteenCenter := by
  intro i hi
  let t := finThirteen.triangleOfPair a.1 b.1 (by
    intro h
    apply hline
    exact congrArg finThirteenCenterLineOf (Subtype.ext h))
  have ht_center : ∃ i : Fin 3, finThirteen.vertex t i = finThirteenCenter := ⟨i, hi⟩
  have hta : ∃ i : Fin 3, finThirteen.vertex t i = a.1 :=
    (finThirteen.pair_mem_triangleOfPair a.1 b.1 (by
      intro h
      apply hline
      exact congrArg finThirteenCenterLineOf (Subtype.ext h))).1
  have htb : ∃ i : Fin 3, finThirteen.vertex t i = b.1 :=
    (finThirteen.pair_mem_triangleOfPair a.1 b.1 (by
      intro h
      apply hline
      exact congrArg finThirteenCenterLineOf (Subtype.ext h))).2
  have hline_a : finThirteenCenterLineOf a = ⟨t, ht_center⟩ :=
    finThirteenCenterLineOf_eq_of_vertex a ⟨t, ht_center⟩ hta
  have hline_b : finThirteenCenterLineOf b = ⟨t, ht_center⟩ :=
    finThirteenCenterLineOf_eq_of_vertex b ⟨t, ht_center⟩ htb
  exact hline (hline_a.trans hline_b.symm)

private noncomputable def sixTimesMinusFiveSourcePoint
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) (z : ZMod g) : Fin 2 × ZMod g :=
  (finThirteenSideNumber a, z)

private theorem sixTimesMinusFiveInternalVertex_sourcePoint
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) (z : ZMod g) :
    sixTimesMinusFiveInternalVertex (g := g) (finThirteenCenterLineOf a)
      (some (sixTimesMinusFiveSourcePoint a z)) = Sum.inl (a, z) := by
  change Sum.inl (finThirteenSideVertex (finThirteenCenterLineOf a)
    (finThirteenSideNumber a), z) = Sum.inl (a, z)
  rw [finThirteenSideVertex_number]

private noncomputable def sixTimesMinusFiveVertex
    (S : SteinerTripleSystem (Option (Fin 2 × ZMod g))) :
    (finThirteenCenterLine × S.Triangle) ⊕
      (finThirteenPeripheralTriangle × (ZMod g × ZMod g)) →
      Fin 3 → sixTimesMinusFiveCarrier g
  | Sum.inl (t, u) => fun i => sixTimesMinusFiveInternalVertex t (S.vertex u i)
  | Sum.inr (t, p) => sixTimesMinusFiveExternalVertex t p

private theorem sixTimesMinusFiveVertex_injective
    (S : SteinerTripleSystem (Option (Fin 2 × ZMod g)))
    (t : (finThirteenCenterLine × S.Triangle) ⊕
      (finThirteenPeripheralTriangle × (ZMod g × ZMod g))) :
    Function.Injective (sixTimesMinusFiveVertex S t) := by
  cases t with
  | inl q =>
      rcases q with ⟨t, u⟩
      exact (sixTimesMinusFiveInternalVertex_injective (g := g) t).comp (S.vertex_injective u)
  | inr q =>
      rcases q with ⟨t, p⟩
      exact sixTimesMinusFiveExternalVertex_injective (g := g) t p

private theorem sixTimesMinusFive_pair_atom_center
    (S : SteinerTripleSystem (Option (Fin 2 × ZMod g)))
    (a : {a : Fin 13 // a ≠ finThirteenCenter}) (z : ZMod g) :
    ∃! t : (finThirteenCenterLine × S.Triangle) ⊕
      (finThirteenPeripheralTriangle × (ZMod g × ZMod g)),
      (∃ i : Fin 3, sixTimesMinusFiveVertex S t i = Sum.inl (a, z)) ∧
        ∃ j : Fin 3, sixTimesMinusFiveVertex S t j = Sum.inr PUnit.unit := by
  let q := finThirteenCenterLineOf a
  let x := some (sixTimesMinusFiveSourcePoint (g := g) a z)
  let u := S.triangleOfPair x none (by simp [x])
  refine ⟨Sum.inl (q, u), ?_, ?_⟩
  · rcases S.pair_mem_triangleOfPair x none (by simp [x]) with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨⟨i, ?_⟩, ⟨j, ?_⟩⟩
    · change sixTimesMinusFiveInternalVertex q (S.vertex u i) = Sum.inl (a, z)
      have hix : S.vertex u i = x := by simpa [u] using hi
      rw [hix]
      exact sixTimesMinusFiveInternalVertex_sourcePoint (g := g) a z
    · change sixTimesMinusFiveInternalVertex q (S.vertex u j) = Sum.inr PUnit.unit
      rw [hj]
      rfl
  · intro t ht
    rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    cases t with
    | inl r =>
        rcases r with ⟨q', u'⟩
        have hi' : sixTimesMinusFiveInternalVertex q' (S.vertex u' i) = Sum.inl (a, z) := by
          simpa [sixTimesMinusFiveVertex] using hi
        have hj' : sixTimesMinusFiveInternalVertex q' (S.vertex u' j) = Sum.inr PUnit.unit := by
          simpa [sixTimesMinusFiveVertex] using hj
        rcases sixTimesMinusFiveInternalVertex_eq_atom (g := g) q' (S.vertex u' i) a z hi'
          with ⟨k, hk, hside⟩
        have hq : finThirteenCenterLineOf a = q' :=
          finThirteenCenterLineOf_eq_of_sideVertex a q' k hside
        have hknum : k = finThirteenSideNumber a := by
          apply finThirteenSideVertex_injective (finThirteenCenterLineOf a)
          rw [← hq] at hside
          exact hside.trans (finThirteenSideVertex_number a).symm
        have hs_atom : S.vertex u' i = x := by
          dsimp [x, sixTimesMinusFiveSourcePoint]
          simpa [hknum] using hk
        have hs_center : S.vertex u' j = none :=
          sixTimesMinusFiveInternalVertex_eq_center (g := g) q' (S.vertex u' j) hj'
        have hu : u' = u := by
          apply S.eq_triangleOfPair_of_contains x none (by simp [x]) u'
          · exact ⟨i, hs_atom⟩
          · exact ⟨j, hs_center⟩
        apply congrArg Sum.inl
        apply Prod.ext
        · exact hq.symm
        · simpa [hq] using hu
    | inr r =>
        rcases r with ⟨q', p⟩
        have hj' : sixTimesMinusFiveExternalVertex (g := g) q' p j = Sum.inr PUnit.unit := by
          simpa [sixTimesMinusFiveVertex] using hj
        simp [sixTimesMinusFiveExternalVertex] at hj'

private theorem sixTimesMinusFive_pair_atoms_same_line
    (S : SteinerTripleSystem (Option (Fin 2 × ZMod g)))
    (a b : {a : Fin 13 // a ≠ finThirteenCenter}) (z w : ZMod g)
    (hxy : Sum.inl (a, z) ≠ (Sum.inl (b, w) : sixTimesMinusFiveCarrier g))
    (hline : finThirteenCenterLineOf a = finThirteenCenterLineOf b) :
    ∃! t : (finThirteenCenterLine × S.Triangle) ⊕
      (finThirteenPeripheralTriangle × (ZMod g × ZMod g)),
      (∃ i : Fin 3, sixTimesMinusFiveVertex S t i = Sum.inl (a, z)) ∧
        ∃ j : Fin 3, sixTimesMinusFiveVertex S t j = Sum.inl (b, w) := by
  let q := finThirteenCenterLineOf a
  let x := some (sixTimesMinusFiveSourcePoint (g := g) a z)
  let y := some (sixTimesMinusFiveSourcePoint (g := g) b w)
  have hx : sixTimesMinusFiveInternalVertex (g := g) q x = Sum.inl (a, z) := by
    dsimp [q, x]
    exact sixTimesMinusFiveInternalVertex_sourcePoint (g := g) a z
  have hy : sixTimesMinusFiveInternalVertex (g := g) q y = Sum.inl (b, w) := by
    dsimp [q, y]
    rw [hline]
    exact sixTimesMinusFiveInternalVertex_sourcePoint (g := g) b w
  have hxy' : x ≠ y := by
    intro h
    apply hxy
    calc
      Sum.inl (a, z) = sixTimesMinusFiveInternalVertex q x := hx.symm
      _ = sixTimesMinusFiveInternalVertex q y := by rw [h]
      _ = Sum.inl (b, w) := hy
  let u := S.triangleOfPair x y hxy'
  refine ⟨Sum.inl (q, u), ?_, ?_⟩
  · rcases S.pair_mem_triangleOfPair x y hxy' with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨⟨i, by change sixTimesMinusFiveInternalVertex q (S.vertex u i) = _; rw [hi]; exact hx⟩,
      ⟨j, by change sixTimesMinusFiveInternalVertex q (S.vertex u j) = _; rw [hj]; exact hy⟩⟩
  · intro t ht
    rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    cases t with
    | inl r =>
        rcases r with ⟨q', u'⟩
        have hi' : sixTimesMinusFiveInternalVertex q' (S.vertex u' i) = Sum.inl (a, z) := by
          simpa [sixTimesMinusFiveVertex] using hi
        have hj' : sixTimesMinusFiveInternalVertex q' (S.vertex u' j) = Sum.inl (b, w) := by
          simpa [sixTimesMinusFiveVertex] using hj
        rcases sixTimesMinusFiveInternalVertex_eq_atom (g := g) q' (S.vertex u' i) a z hi'
          with ⟨ka, hka, hsidea⟩
        rcases sixTimesMinusFiveInternalVertex_eq_atom (g := g) q' (S.vertex u' j) b w hj'
          with ⟨kb, hkb, hsideb⟩
        have hqa : finThirteenCenterLineOf a = q' :=
          finThirteenCenterLineOf_eq_of_sideVertex a q' ka hsidea
        have hqb : finThirteenCenterLineOf b = q' :=
          finThirteenCenterLineOf_eq_of_sideVertex b q' kb hsideb
        have hka_number : ka = finThirteenSideNumber a := by
          apply finThirteenSideVertex_injective (finThirteenCenterLineOf a)
          rw [← hqa] at hsidea
          exact hsidea.trans (finThirteenSideVertex_number a).symm
        have hkb_number : kb = finThirteenSideNumber b := by
          apply finThirteenSideVertex_injective (finThirteenCenterLineOf b)
          rw [← hqb] at hsideb
          exact hsideb.trans (finThirteenSideVertex_number b).symm
        have hsx : S.vertex u' i = x := by
          dsimp [x, sixTimesMinusFiveSourcePoint]
          simpa [hka_number] using hka
        have hsy : S.vertex u' j = y := by
          dsimp [y, sixTimesMinusFiveSourcePoint]
          simpa [hkb_number] using hkb
        have hu : u' = u := by
          apply S.eq_triangleOfPair_of_contains x y hxy' u'
          · exact ⟨i, hsx⟩
          · exact ⟨j, hsy⟩
        apply congrArg Sum.inl
        apply Prod.ext
        · exact hqa.symm
        · simpa [q, hqa] using hu
    | inr r =>
        rcases r with ⟨q', p⟩
        have hi' : sixTimesMinusFiveExternalVertex (g := g) q' p i = Sum.inl (a, z) := by
          simpa [sixTimesMinusFiveVertex] using hi
        have hj' : sixTimesMinusFiveExternalVertex (g := g) q' p j = Sum.inl (b, w) := by
          simpa [sixTimesMinusFiveVertex] using hj
        rcases sixTimesMinusFiveExternalVertex_eq_atom (g := g) q' p i a z hi' with ⟨hia, _⟩
        rcases sixTimesMinusFiveExternalVertex_eq_atom (g := g) q' p j b w hj' with ⟨hjb, _⟩
        by_cases hab : a = b
        · subst b
          have hij : i = j := finThirteen.vertex_injective q'.1 (hia.trans hjb.symm)
          subst j
          exact False.elim (hxy (hi.symm.trans hj))
        · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
          have hline_a : ∃ k : Fin 3,
              finThirteen.vertex (finThirteenCenterLineOf a).1 k = a.1 :=
            ⟨(finThirteenSideEquiv (finThirteenCenterLineOf a)
              (finThirteenSideNumber a)).1,
              congrArg Subtype.val (finThirteenSideVertex_number a)⟩
          have hline_b0 : ∃ k : Fin 3,
              finThirteen.vertex (finThirteenCenterLineOf b).1 k = b.1 :=
            ⟨(finThirteenSideEquiv (finThirteenCenterLineOf b)
              (finThirteenSideNumber b)).1,
              congrArg Subtype.val (finThirteenSideVertex_number b)⟩
          have hline_b : ∃ k : Fin 3,
              finThirteen.vertex (finThirteenCenterLineOf a).1 k = b.1 := by
            rw [hline]
            exact hline_b0
          have hq_pair := finThirteen.eq_triangleOfPair_of_contains a.1 b.1 hab' q'.1
            ⟨i, hia⟩ ⟨j, hjb⟩
          have hline_pair := finThirteen.eq_triangleOfPair_of_contains a.1 b.1 hab'
            (finThirteenCenterLineOf a).1 hline_a hline_b
          have hq_base : q'.1 = (finThirteenCenterLineOf a).1 :=
            hq_pair.trans hline_pair.symm
          rcases (finThirteenCenterLineOf a).2 with ⟨k, hk⟩
          exact False.elim (q'.2 k (by simpa [hq_base] using hk))

private theorem sixTimesMinusFive_pair_atoms_distinct_lines
    (S : SteinerTripleSystem (Option (Fin 2 × ZMod g)))
    (a b : {a : Fin 13 // a ≠ finThirteenCenter}) (z w : ZMod g)
    (hline : finThirteenCenterLineOf a ≠ finThirteenCenterLineOf b) :
    ∃! t : (finThirteenCenterLine × S.Triangle) ⊕
      (finThirteenPeripheralTriangle × (ZMod g × ZMod g)),
      (∃ i : Fin 3, sixTimesMinusFiveVertex S t i = Sum.inl (a, z)) ∧
        ∃ j : Fin 3, sixTimesMinusFiveVertex S t j = Sum.inl (b, w) := by
  have hab : a.1 ≠ b.1 := by
    intro h
    apply hline
    exact congrArg finThirteenCenterLineOf (Subtype.ext h)
  let u := finThirteen.triangleOfPair a.1 b.1 hab
  have hu_peripheral : ∀ i : Fin 3, finThirteen.vertex u i ≠ finThirteenCenter := by
    simpa [u] using finThirteen_triangleOfPair_peripheral_of_distinct_lines a b hline
  let q : finThirteenPeripheralTriangle := ⟨u, hu_peripheral⟩
  let ia := (finThirteen.pair_mem_triangleOfPair a.1 b.1 hab).1.choose
  let ib := (finThirteen.pair_mem_triangleOfPair a.1 b.1 hab).2.choose
  have hia : finThirteen.vertex u ia = a.1 := by
    exact (finThirteen.pair_mem_triangleOfPair a.1 b.1 hab).1.choose_spec
  have hib : finThirteen.vertex u ib = b.1 := by
    exact (finThirteen.pair_mem_triangleOfPair a.1 b.1 hab).2.choose_spec
  have hiab : ia ≠ ib := by
    intro h
    apply hab
    rw [← hia, ← hib, h]
  rcases existsUnique_triplingCross_of_distinct ia ib z w hiab with ⟨p, hp, hpuniq⟩
  refine ⟨Sum.inr (q, p), ?_, ?_⟩
  · rcases hp with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have hii : i = ia := triplingCrossVertex_index_eq_fst hi
    have hij : j = ib := triplingCrossVertex_index_eq_fst hj
    subst i
    subst j
    refine ⟨⟨ia, ?_⟩, ⟨ib, ?_⟩⟩
    · change Sum.inl (⟨finThirteen.vertex q.1 ia, q.2 ia⟩,
          (triplingCrossVertex p ia).2) = Sum.inl (a, z)
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Subtype.ext
        simpa [q] using hia
      · exact congrArg (fun r : Fin 3 × ZMod g => r.2) hi
    · change Sum.inl (⟨finThirteen.vertex q.1 ib, q.2 ib⟩,
          (triplingCrossVertex p ib).2) = Sum.inl (b, w)
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Subtype.ext
        simpa [q] using hib
      · exact congrArg (fun r : Fin 3 × ZMod g => r.2) hj
  · intro t ht
    rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    cases t with
    | inl r =>
        rcases r with ⟨q', u'⟩
        have hi' : sixTimesMinusFiveInternalVertex q' (S.vertex u' i) = Sum.inl (a, z) := by
          simpa [sixTimesMinusFiveVertex] using hi
        have hj' : sixTimesMinusFiveInternalVertex q' (S.vertex u' j) = Sum.inl (b, w) := by
          simpa [sixTimesMinusFiveVertex] using hj
        rcases sixTimesMinusFiveInternalVertex_eq_atom (g := g) q' (S.vertex u' i) a z hi'
          with ⟨ka, hka, hsidea⟩
        rcases sixTimesMinusFiveInternalVertex_eq_atom (g := g) q' (S.vertex u' j) b w hj'
          with ⟨kb, hkb, hsideb⟩
        have hqa : finThirteenCenterLineOf a = q' :=
          finThirteenCenterLineOf_eq_of_sideVertex a q' ka hsidea
        have hqb : finThirteenCenterLineOf b = q' :=
          finThirteenCenterLineOf_eq_of_sideVertex b q' kb hsideb
        exact False.elim (hline (hqa.trans hqb.symm))
    | inr r =>
        rcases r with ⟨q', p'⟩
        have hi' : sixTimesMinusFiveExternalVertex (g := g) q' p' i = Sum.inl (a, z) := by
          simpa [sixTimesMinusFiveVertex] using hi
        have hj' : sixTimesMinusFiveExternalVertex (g := g) q' p' j = Sum.inl (b, w) := by
          simpa [sixTimesMinusFiveVertex] using hj
        rcases sixTimesMinusFiveExternalVertex_eq_atom (g := g) q' p' i a z hi'
          with ⟨hia', hza⟩
        rcases sixTimesMinusFiveExternalVertex_eq_atom (g := g) q' p' j b w hj'
          with ⟨hib', hwb⟩
        have hq_base : q'.1 = u := by
          exact finThirteen.eq_triangleOfPair_of_contains a.1 b.1 hab q'.1
            ⟨i, hia'⟩ ⟨j, hib'⟩
        have hq : q' = q := by
          apply Subtype.ext
          simpa [q] using hq_base
        have hia_u : finThirteen.vertex u i = a.1 := by
          simpa [hq_base] using hia'
        have hib_u : finThirteen.vertex u j = b.1 := by
          simpa [hq_base] using hib'
        have hiai : i = ia := finThirteen.vertex_injective u (hia_u.trans hia.symm)
        have hibj : j = ib := finThirteen.vertex_injective u (hib_u.trans hib.symm)
        subst i
        subst j
        have hfst_a : (triplingCrossVertex p' ia).1 = ia := by
          symm
          exact triplingCrossVertex_index_eq_fst (p := p')
            (i := ia) (a := (triplingCrossVertex p' ia).1)
            (x := (triplingCrossVertex p' ia).2) rfl
        have hpa : triplingCrossVertex p' ia = (ia, z) :=
          Prod.ext hfst_a hza
        have hfst_b : (triplingCrossVertex p' ib).1 = ib := by
          symm
          exact triplingCrossVertex_index_eq_fst (p := p')
            (i := ib) (a := (triplingCrossVertex p' ib).1)
            (x := (triplingCrossVertex p' ib).2) rfl
        have hpb : triplingCrossVertex p' ib = (ib, w) :=
          Prod.ext hfst_b hwb
        have hp' : p' = p := hpuniq p' ⟨⟨ia, hpa⟩, ⟨ib, hpb⟩⟩
        apply congrArg Sum.inr
        exact Prod.ext hq hp'

private theorem sixTimesMinusFive_pair_covered_once
    (S : SteinerTripleSystem (Option (Fin 2 × ZMod g))) :
    ∀ x y : sixTimesMinusFiveCarrier g, x ≠ y →
      ∃! t : (finThirteenCenterLine × S.Triangle) ⊕
        (finThirteenPeripheralTriangle × (ZMod g × ZMod g)),
        (∃ i : Fin 3, sixTimesMinusFiveVertex S t i = x) ∧
          ∃ j : Fin 3, sixTimesMinusFiveVertex S t j = y := by
  intro x y hxy
  cases x with
  | inl ax =>
      rcases ax with ⟨a, z⟩
      cases y with
      | inl bw =>
          rcases bw with ⟨b, w⟩
          by_cases hline : finThirteenCenterLineOf a = finThirteenCenterLineOf b
          · exact sixTimesMinusFive_pair_atoms_same_line S a b z w hxy hline
          · exact sixTimesMinusFive_pair_atoms_distinct_lines S a b z w hline
      | inr y =>
          cases y
          exact sixTimesMinusFive_pair_atom_center S a z
  | inr x =>
      cases x
      cases y with
      | inl bw =>
          rcases bw with ⟨b, w⟩
          rcases sixTimesMinusFive_pair_atom_center S b w with ⟨t, ht, htuniq⟩
          refine ⟨t, ⟨ht.2, ht.1⟩, ?_⟩
          intro t' ht'
          exact htuniq t' ⟨ht'.2, ht'.1⟩
      | inr y =>
          cases y
          exact False.elim (hxy rfl)

/-- Feder--Subi Lemma 7 on its natural grouped carrier: an `STS(2g+1)`
supplies the six shared-center group fillings, and every remaining base
triangle is expanded by the cyclic transversal construction. -/
noncomputable def sixTimesMinusFive
    (S : SteinerTripleSystem (Option (Fin 2 × ZMod g))) :
    SteinerTripleSystem (sixTimesMinusFiveCarrier g) where
  Triangle := (finThirteenCenterLine × S.Triangle) ⊕
    (finThirteenPeripheralTriangle × (ZMod g × ZMod g))
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := sixTimesMinusFiveVertex S
  vertex_injective := sixTimesMinusFiveVertex_injective S
  pair_covered_once := sixTimesMinusFive_pair_covered_once S

private theorem card_finThirteenNoncentral :
    Fintype.card {a : Fin 13 // a ≠ finThirteenCenter} = 12 := by
  decide

private theorem card_sixTimesMinusFiveCarrier :
    Fintype.card (sixTimesMinusFiveCarrier g) = 6 * (2 * g + 1) - 5 := by
  rw [Fintype.card_sum, Fintype.card_prod, card_finThirteenNoncentral, ZMod.card,
    Fintype.card_punit]
  omega

private theorem card_sixTimesMinusFiveSource :
    Fintype.card (Option (Fin 2 × ZMod g)) = 2 * g + 1 := by
  rw [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, ZMod.card]

/-- Feder--Subi Lemma 7 with finite labels: `STS(2g+1) -> STS(6(2g+1)-5)`
for positive `g`. The `g = 0` source case and target are both the trivial
one-point system and are handled separately in the cardinality induction. -/
noncomputable def sixTimesMinusFiveFinOfFin
    (S : SteinerTripleSystem (Fin (2 * g + 1))) :
    SteinerTripleSystem (Fin (6 * (2 * g + 1) - 5)) :=
  let sourceRelabel : Option (Fin 2 × ZMod g) ≃ Fin (2 * g + 1) :=
    Fintype.equivFinOfCardEq card_sixTimesMinusFiveSource
  SteinerTripleSystem.map
    (Fintype.equivFinOfCardEq card_sixTimesMinusFiveCarrier)
    (sixTimesMinusFive (SteinerTripleSystem.map sourceRelabel.symm S))

end SixTimesMinusFive

section TripleWaleckiExtension

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (F : OneFactorization β α)

/-- The carrier of the threefold Walecki extension: the left system already
has three points above each factor, and every right point is expanded to its
own three-point block. -/
private abbrev tripleWaleckiCarrier := (ZMod 3 × α) ⊕ (ZMod 3 × β)

private def finToZModThree (i : Fin 3) : ZMod 3 := i.1

private theorem finToZModThree_injective : Function.Injective finToZModThree := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg (ZMod.val : ZMod 3 → ℕ) hij
  simpa [finToZModThree, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hval

private def tripleWaleckiRightVertex (b : β) :
    Fin 3 → tripleWaleckiCarrier (α := α) (β := β) :=
  fun i => Sum.inr (finToZModThree i, b)

private theorem tripleWaleckiRightVertex_injective (b : β) :
    Function.Injective (tripleWaleckiRightVertex (α := α) b) := by
  intro i j hij
  apply finToZModThree_injective
  exact congrArg Prod.fst (Sum.inr.inj hij)

/-- The nine transversal triples replacing a super-triangle consisting of a
left block and the two endpoints of a factorization edge. -/
noncomputable def tripleWaleckiCrossVertex (e : OffDiagonalPair β)
    (p : ZMod 3 × ZMod 3) :
    Fin 3 → tripleWaleckiCarrier (α := α) (β := β) := fun i =>
  if i = 0 then Sum.inl ((triplingCrossVertex p i).2, F.factorOfEdge e)
  else if i = 1 then Sum.inr ((triplingCrossVertex p i).2, e.first)
  else Sum.inr ((triplingCrossVertex p i).2, e.second)

@[simp] private theorem tripleWaleckiCrossVertex_zero (e : OffDiagonalPair β)
    (p : ZMod 3 × ZMod 3) :
    tripleWaleckiCrossVertex F e p 0 = Sum.inl (p.1, F.factorOfEdge e) := by
  simp [tripleWaleckiCrossVertex, triplingCrossVertex]

@[simp] private theorem tripleWaleckiCrossVertex_one (e : OffDiagonalPair β)
    (p : ZMod 3 × ZMod 3) :
    tripleWaleckiCrossVertex F e p 1 = Sum.inr (p.2, e.first) := by
  simp [tripleWaleckiCrossVertex, triplingCrossVertex]

@[simp] private theorem tripleWaleckiCrossVertex_two (e : OffDiagonalPair β)
    (p : ZMod 3 × ZMod 3) :
    tripleWaleckiCrossVertex F e p 2 = Sum.inr (p.1 + p.2, e.second) := by
  simp [tripleWaleckiCrossVertex, triplingCrossVertex]

private theorem tripleWaleckiCrossVertex_injective (e : OffDiagonalPair β)
    (p : ZMod 3 × ZMod 3) : Function.Injective (tripleWaleckiCrossVertex F e p) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hij ⊢
  · exact False.elim (e.first_ne_second hij.2)
  · exact False.elim (e.first_ne_second hij.2.symm)

private theorem tripleWaleckiCross_left_index {e : OffDiagonalPair β}
    {p : ZMod 3 × ZMod 3} {i : Fin 3} {x : ZMod 3} {a : α}
    (h : tripleWaleckiCrossVertex F e p i = Sum.inl (x, a)) : i = 0 := by
  fin_cases i <;> simp [tripleWaleckiCrossVertex, triplingCrossVertex] at h ⊢

private theorem tripleWaleckiCross_left_factor {e : OffDiagonalPair β}
    {p : ZMod 3 × ZMod 3} {i : Fin 3} {x : ZMod 3} {a : α}
    (h : tripleWaleckiCrossVertex F e p i = Sum.inl (x, a)) : F.factorOfEdge e = a := by
  have hi := tripleWaleckiCross_left_index (F := F) h
  subst i
  have h' : p.1 = x ∧ F.factorOfEdge e = a := by
    simpa [tripleWaleckiCrossVertex, triplingCrossVertex] using h
  exact h'.2

private theorem tripleWaleckiCross_right_mem {e : OffDiagonalPair β}
    {p : ZMod 3 × ZMod 3} {i : Fin 3} {x : ZMod 3} {b : β}
    (h : tripleWaleckiCrossVertex F e p i = Sum.inr (x, b)) : b ∈ e.1 := by
  fin_cases i
  · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at h
  · have h' : p.2 = x ∧ e.first = b := by
      simpa [tripleWaleckiCrossVertex, triplingCrossVertex] using h
    rw [← h'.2]
    exact e.1.out_fst_mem
  · have h' : p.1 + p.2 = x ∧ e.second = b := by
      simpa [tripleWaleckiCrossVertex, triplingCrossVertex] using h
    rw [← h'.2]
    exact e.1.out_snd_mem

private theorem existsUnique_tripleWaleckiCross_left_right
    (x : ZMod 3) (a : α) (y : ZMod 3) (b : β) :
    ∃! q : OffDiagonalPair β × (ZMod 3 × ZMod 3),
      (∃ i : Fin 3, tripleWaleckiCrossVertex F q.1 q.2 i = Sum.inl (x, a)) ∧
        ∃ j : Fin 3, tripleWaleckiCrossVertex F q.1 q.2 j = Sum.inr (y, b) := by
  let c : β := (F.matching a).perm b
  have hbc : b ≠ c := (F.matching a).apply_ne b |>.symm
  let e₀ : OffDiagonalPair β := OffDiagonalPair.mk b c hbc
  have hfactor : F.factorOfEdge e₀ = a := by
    exact (F.factorOfEdge_mk_eq b c hbc a rfl).symm
  rcases (e₀.mem_iff_first_or_second b).mp (OffDiagonalPair.mem_mk_left b c hbc) with hfirst | hsecond
  · refine ⟨(e₀, (x, y)), ?_, ?_⟩
    · exact ⟨⟨0, by simp [tripleWaleckiCrossVertex, hfactor]⟩,
        ⟨1, by simpa [tripleWaleckiCrossVertex, hfirst]⟩⟩
    · intro q hq
      rcases q with ⟨e, p⟩
      rcases hq with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      have hfactor' : F.factorOfEdge e = a := tripleWaleckiCross_left_factor F hi
      have hbmem : b ∈ e.1 := tripleWaleckiCross_right_mem F hj
      have hedge : e.1 = s(b, c) := by
        rcases (e.mem_iff_first_or_second b).mp hbmem with hefirst | hesecond
        · have hpartner : (F.matching a).perm e.first = e.second := by
            rw [← hfactor']
            exact F.matching_factorOfEdge_first e
          have hpartner' : e.second = c := by
            simpa [c, hefirst] using hpartner.symm
          calc
            e.1 = s(e.first, e.second) := e.mk_first_second.symm
            _ = s(b, c) := by rw [hefirst, hpartner']
        · have hpartner : (F.matching a).perm e.second = e.first := by
            rw [← hfactor']
            exact F.matching_factorOfEdge_second e
          have hpartner' : e.first = c := by
            simpa [c, hesecond] using hpartner.symm
          calc
            e.1 = s(e.first, e.second) := e.mk_first_second.symm
            _ = s(c, b) := by rw [hesecond, hpartner']
            _ = s(b, c) := Sym2.eq_swap
      have he : e = e₀ := by
        apply Subtype.ext
        simpa [e₀] using hedge
      subst e
      have hi0 : i = 0 := tripleWaleckiCross_left_index (F := F) hi
      subst i
      have hj1 : j = 1 := by
        fin_cases j
        · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hj
        · rfl
        · have hparsed : p.1 + p.2 = y ∧ e₀.second = e₀.first := by
            simpa [tripleWaleckiCrossVertex, triplingCrossVertex, hfirst] using hj
          have hbad : e₀.second = e₀.first := hparsed.2
          exact False.elim (e₀.first_ne_second hbad.symm)
      subst j
      have hp1 : p.1 = x := by
        simpa [tripleWaleckiCrossVertex, hfactor, triplingCrossVertex] using hi
      have hp2 : p.2 = y := by
        simpa [tripleWaleckiCrossVertex, hfirst, triplingCrossVertex] using hj
      apply Prod.ext
      · rfl
      · exact Prod.ext hp1 hp2
  · refine ⟨(e₀, (x, y - x)), ?_, ?_⟩
    · refine ⟨⟨0, by simp [tripleWaleckiCrossVertex, hfactor]⟩, ⟨2, ?_⟩⟩
      simp [tripleWaleckiCrossVertex, hsecond, triplingCrossVertex]
    · intro q hq
      rcases q with ⟨e, p⟩
      rcases hq with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      have hfactor' : F.factorOfEdge e = a := tripleWaleckiCross_left_factor F hi
      have hbmem : b ∈ e.1 := tripleWaleckiCross_right_mem F hj
      have hedge : e.1 = s(b, c) := by
        rcases (e.mem_iff_first_or_second b).mp hbmem with hefirst | hesecond
        · have hpartner : (F.matching a).perm e.first = e.second := by
            rw [← hfactor']
            exact F.matching_factorOfEdge_first e
          have hpartner' : e.second = c := by
            simpa [c, hefirst] using hpartner.symm
          calc
            e.1 = s(e.first, e.second) := e.mk_first_second.symm
            _ = s(b, c) := by rw [hefirst, hpartner']
        · have hpartner : (F.matching a).perm e.second = e.first := by
            rw [← hfactor']
            exact F.matching_factorOfEdge_second e
          have hpartner' : e.first = c := by
            simpa [c, hesecond] using hpartner.symm
          calc
            e.1 = s(e.first, e.second) := e.mk_first_second.symm
            _ = s(c, b) := by rw [hesecond, hpartner']
            _ = s(b, c) := Sym2.eq_swap
      have he : e = e₀ := by
        apply Subtype.ext
        simpa [e₀] using hedge
      subst e
      have hi0 : i = 0 := tripleWaleckiCross_left_index (F := F) hi
      subst i
      have hj2 : j = 2 := by
        fin_cases j
        · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hj
        · have hparsed : p.2 = y ∧ e₀.first = e₀.second := by
            simpa [tripleWaleckiCrossVertex, triplingCrossVertex, hsecond] using hj
          have hbad : e₀.first = e₀.second := hparsed.2
          exact False.elim (e₀.first_ne_second hbad)
        · rfl
      subst j
      have hp1 : p.1 = x := by
        simpa [tripleWaleckiCrossVertex, hfactor, triplingCrossVertex] using hi
      have hsum : p.1 + p.2 = y := by
        simpa [tripleWaleckiCrossVertex, hsecond, triplingCrossVertex] using hj
      have hp2 : p.2 = y - x := by
        calc
          p.2 = (p.1 + p.2) - p.1 := by abel
          _ = y - x := by rw [hsum, hp1]
      apply Prod.ext
      · rfl
      · exact Prod.ext hp1 hp2

private theorem existsUnique_tripleWaleckiCross_right_right
    (x : ZMod 3) (b : β) (y : ZMod 3) (b' : β) (hbb' : b ≠ b') :
    ∃! q : OffDiagonalPair β × (ZMod 3 × ZMod 3),
      (∃ i : Fin 3, tripleWaleckiCrossVertex F q.1 q.2 i = Sum.inr (x, b)) ∧
        ∃ j : Fin 3, tripleWaleckiCrossVertex F q.1 q.2 j = Sum.inr (y, b') := by
  let e₀ : OffDiagonalPair β := OffDiagonalPair.mk b b' hbb'
  rcases (e₀.mem_iff_first_or_second b).mp (OffDiagonalPair.mem_mk_left b b' hbb') with hfirst | hsecond
  · have hsecond' : b' = e₀.second := by
      rcases (e₀.mem_iff_first_or_second b').mp (OffDiagonalPair.mem_mk_right b b' hbb') with h | h
      · exact False.elim (hbb' (hfirst.trans h.symm))
      · exact h
    refine ⟨(e₀, (y - x, x)), ?_, ?_⟩
    · refine ⟨⟨1, by simpa [tripleWaleckiCrossVertex, hfirst]⟩, ⟨2, ?_⟩⟩
      simp [tripleWaleckiCrossVertex, hsecond', triplingCrossVertex]
    · intro q hq
      rcases q with ⟨e, p⟩
      rcases hq with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      have hbmem : b ∈ e.1 := tripleWaleckiCross_right_mem F hi
      have hb'mem : b' ∈ e.1 := tripleWaleckiCross_right_mem F hj
      have he : e = e₀ := by
        apply Subtype.ext
        apply (Sym2.mem_and_mem_iff hbb').mp
        exact ⟨hbmem, hb'mem⟩
      subst e
      have hi1 : i = 1 := by
        fin_cases i
        · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hi
        · rfl
        · have hparsed : p.1 + p.2 = x ∧ e₀.second = e₀.first := by
            simpa [tripleWaleckiCrossVertex, triplingCrossVertex, hfirst] using hi
          exact False.elim (e₀.first_ne_second hparsed.2.symm)
      have hj2 : j = 2 := by
        fin_cases j
        · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hj
        · have hparsed : p.2 = y ∧ e₀.first = e₀.second := by
            simpa [tripleWaleckiCrossVertex, triplingCrossVertex, hsecond'] using hj
          exact False.elim (e₀.first_ne_second hparsed.2)
        · rfl
      subst i
      subst j
      have hp2 : p.2 = x := by
        simpa [tripleWaleckiCrossVertex, hfirst, triplingCrossVertex] using hi
      have hsum : p.1 + p.2 = y := by
        simpa [tripleWaleckiCrossVertex, hsecond', triplingCrossVertex] using hj
      have hp1 : p.1 = y - x := by
        calc
          p.1 = (p.1 + p.2) - p.2 := by abel
          _ = y - x := by rw [hsum, hp2]
      apply Prod.ext
      · rfl
      · exact Prod.ext hp1 hp2
  · have hfirst' : b' = e₀.first := by
      rcases (e₀.mem_iff_first_or_second b').mp (OffDiagonalPair.mem_mk_right b b' hbb') with h | h
      · exact h
      · exact False.elim (hbb' (hsecond.trans h.symm))
    refine ⟨(e₀, (x - y, y)), ?_, ?_⟩
    · refine ⟨⟨2, ?_⟩, ⟨1, by simpa [tripleWaleckiCrossVertex, hfirst']⟩⟩
      simp [tripleWaleckiCrossVertex, hsecond, triplingCrossVertex]
    · intro q hq
      rcases q with ⟨e, p⟩
      rcases hq with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      have hbmem : b ∈ e.1 := tripleWaleckiCross_right_mem F hi
      have hb'mem : b' ∈ e.1 := tripleWaleckiCross_right_mem F hj
      have he : e = e₀ := by
        apply Subtype.ext
        apply (Sym2.mem_and_mem_iff hbb').mp
        exact ⟨hbmem, hb'mem⟩
      subst e
      have hi2 : i = 2 := by
        fin_cases i
        · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hi
        · have hparsed : p.2 = x ∧ e₀.first = e₀.second := by
            simpa [tripleWaleckiCrossVertex, triplingCrossVertex, hsecond] using hi
          exact False.elim (e₀.first_ne_second hparsed.2)
        · rfl
      have hj1 : j = 1 := by
        fin_cases j
        · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hj
        · rfl
        · have hparsed : p.1 + p.2 = y ∧ e₀.second = e₀.first := by
            simpa [tripleWaleckiCrossVertex, triplingCrossVertex, hfirst'] using hj
          exact False.elim (e₀.first_ne_second hparsed.2.symm)
      subst i
      subst j
      have hsum : p.1 + p.2 = x := by
        simpa [tripleWaleckiCrossVertex, hsecond, triplingCrossVertex] using hi
      have hp2 : p.2 = y := by
        simpa [tripleWaleckiCrossVertex, hfirst', triplingCrossVertex] using hj
      have hp1 : p.1 = x - y := by
        calc
          p.1 = (p.1 + p.2) - p.2 := by abel
          _ = x - y := by rw [hsum, hp2]
      apply Prod.ext
      · rfl
      · exact Prod.ext hp1 hp2

private theorem tripleWaleckiCross_two_left_equal {e : OffDiagonalPair β}
    {p : ZMod 3 × ZMod 3} {i j : Fin 3} {x y : ZMod 3} {a b : α}
    (hi : tripleWaleckiCrossVertex F e p i = Sum.inl (x, a))
    (hj : tripleWaleckiCrossVertex F e p j = Sum.inl (y, b)) :
    (Sum.inl (x, a) : tripleWaleckiCarrier (α := α) (β := β)) = Sum.inl (y, b) := by
  have hi0 : i = 0 := tripleWaleckiCross_left_index (F := F) hi
  have hj0 : j = 0 := tripleWaleckiCross_left_index (F := F) hj
  subst i
  subst j
  exact hi.symm.trans hj

private theorem tripleWaleckiCross_two_same_right_equal {e : OffDiagonalPair β}
    {p : ZMod 3 × ZMod 3} {i j : Fin 3} {x y : ZMod 3} {b : β}
    (hi : tripleWaleckiCrossVertex F e p i = Sum.inr (x, b))
    (hj : tripleWaleckiCrossVertex F e p j = Sum.inr (y, b)) :
    (Sum.inr (x, b) : tripleWaleckiCarrier (α := α) (β := β)) = Sum.inr (y, b) := by
  fin_cases i
  · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hi
  · fin_cases j
    · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hj
    · exact hi.symm.trans hj
    · have hiparsed : p.2 = x ∧ e.first = b := by
        simpa [tripleWaleckiCrossVertex, triplingCrossVertex] using hi
      have hjparsed : p.1 + p.2 = y ∧ e.second = b := by
        simpa [tripleWaleckiCrossVertex, triplingCrossVertex] using hj
      have hfirst : e.first = b := hiparsed.2
      have hsecond : e.second = b := hjparsed.2
      exact False.elim (e.first_ne_second (hfirst.trans hsecond.symm))
  · fin_cases j
    · simp [tripleWaleckiCrossVertex, triplingCrossVertex] at hj
    · have hiparsed : p.1 + p.2 = x ∧ e.second = b := by
        simpa [tripleWaleckiCrossVertex, triplingCrossVertex] using hi
      have hjparsed : p.2 = y ∧ e.first = b := by
        simpa [tripleWaleckiCrossVertex, triplingCrossVertex] using hj
      have hsecond : e.second = b := hiparsed.2
      have hfirst : e.first = b := hjparsed.2
      exact False.elim (e.first_ne_second (hfirst.trans hsecond.symm))
    · exact hi.symm.trans hj

private noncomputable def tripleWaleckiExtensionVertex
    (S : SteinerTripleSystem (ZMod 3 × α)) :
    S.Triangle ⊕ (β ⊕ (OffDiagonalPair β × (ZMod 3 × ZMod 3))) →
      Fin 3 → tripleWaleckiCarrier (α := α) (β := β)
  | Sum.inl t => fun i => Sum.inl (S.vertex t i)
  | Sum.inr (Sum.inl b) => tripleWaleckiRightVertex b
  | Sum.inr (Sum.inr (e, p)) => tripleWaleckiCrossVertex F e p

private theorem tripleWaleckiExtensionVertex_injective
    (S : SteinerTripleSystem (ZMod 3 × α))
    (t : S.Triangle ⊕ (β ⊕ (OffDiagonalPair β × (ZMod 3 × ZMod 3)))) :
    Function.Injective (tripleWaleckiExtensionVertex F S t) := by
  cases t with
  | inl t =>
      intro i j hij
      apply S.vertex_injective t
      exact Sum.inl.inj hij
  | inr t =>
      cases t with
      | inl b => exact tripleWaleckiRightVertex_injective b
      | inr q =>
          rcases q with ⟨e, p⟩
          exact tripleWaleckiCrossVertex_injective F e p

private theorem tripleWaleckiExtension_pair_covered_once
    (S : SteinerTripleSystem (ZMod 3 × α)) :
    ∀ x y : tripleWaleckiCarrier (α := α) (β := β), x ≠ y →
      ∃! t : S.Triangle ⊕ (β ⊕ (OffDiagonalPair β × (ZMod 3 × ZMod 3))),
        (∃ i : Fin 3, tripleWaleckiExtensionVertex F S t i = x) ∧
          ∃ j : Fin 3, tripleWaleckiExtensionVertex F S t j = y := by
  intro x y hxy
  cases x with
  | inl ax =>
      rcases ax with ⟨x, a⟩
      cases y with
      | inl ay =>
          rcases ay with ⟨y, b⟩
          have hxy' : (x, a) ≠ (y, b) := by
            intro h
            apply hxy
            exact congrArg Sum.inl h
          let t₀ := S.triangleOfPair (x, a) (y, b) hxy'
          refine ⟨Sum.inl t₀, ?_, ?_⟩
          · rcases S.pair_mem_triangleOfPair (x, a) (y, b) hxy' with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            exact ⟨⟨i, congrArg Sum.inl hi⟩, ⟨j, congrArg Sum.inl hj⟩⟩
          · intro t ht
            rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
            cases t with
            | inl t =>
                apply congrArg Sum.inl
                apply S.eq_triangleOfPair_of_contains (x, a) (y, b) hxy' t
                · exact ⟨i, Sum.inl.inj hi⟩
                · exact ⟨j, Sum.inl.inj hj⟩
            | inr t =>
                cases t with
                | inl b' =>
                    simp [tripleWaleckiExtensionVertex, tripleWaleckiRightVertex] at hi
                | inr q =>
                    rcases q with ⟨e, p⟩
                    exact False.elim (hxy (tripleWaleckiCross_two_left_equal F hi hj))
      | inr by_ =>
          rcases by_ with ⟨y, b⟩
          rcases existsUnique_tripleWaleckiCross_left_right F x a y b with ⟨q, hq, hquniq⟩
          refine ⟨Sum.inr (Sum.inr q), hq, ?_⟩
          intro t ht
          cases t with
          | inl t =>
              rcases ht.2 with ⟨j, hj⟩
              simp [tripleWaleckiExtensionVertex] at hj
          | inr t =>
              cases t with
              | inl b' =>
                  rcases ht.1 with ⟨i, hi⟩
                  simp [tripleWaleckiExtensionVertex, tripleWaleckiRightVertex] at hi
              | inr q' =>
                  apply congrArg (fun r => Sum.inr (Sum.inr r))
                  exact hquniq q' ht
  | inr bx =>
      rcases bx with ⟨x, b⟩
      cases y with
      | inl ay =>
          rcases ay with ⟨y, a⟩
          rcases existsUnique_tripleWaleckiCross_left_right F y a x b with ⟨q, hq, hquniq⟩
          refine ⟨Sum.inr (Sum.inr q), ⟨hq.2, hq.1⟩, ?_⟩
          intro t ht
          cases t with
          | inl t =>
              rcases ht.1 with ⟨i, hi⟩
              simp [tripleWaleckiExtensionVertex] at hi
          | inr t =>
              cases t with
              | inl b' =>
                  rcases ht.2 with ⟨j, hj⟩
                  simp [tripleWaleckiExtensionVertex, tripleWaleckiRightVertex] at hj
              | inr q' =>
                  apply congrArg (fun r => Sum.inr (Sum.inr r))
                  apply hquniq q'
                  exact ⟨ht.2, ht.1⟩
      | inr by_ =>
          rcases by_ with ⟨y, b'⟩
          by_cases hbb' : b = b'
          · subst b'
            have hxy' : x ≠ y := by
              intro h
              apply hxy
              simpa [h]
            refine ⟨Sum.inr (Sum.inl b), ?_, ?_⟩
            · let ix : Fin 3 := ⟨x.val, x.val_lt⟩
              let iy : Fin 3 := ⟨y.val, y.val_lt⟩
              have hix : finToZModThree ix = x := by
                apply ZMod.val_injective 3
                simpa [finToZModThree, ix] using (ZMod.val_natCast_of_lt x.val_lt)
              have hiy : finToZModThree iy = y := by
                apply ZMod.val_injective 3
                simpa [finToZModThree, iy] using (ZMod.val_natCast_of_lt y.val_lt)
              exact ⟨⟨ix, by simpa [tripleWaleckiExtensionVertex,
                tripleWaleckiRightVertex] using hix⟩,
                ⟨iy, by simpa [tripleWaleckiExtensionVertex,
                  tripleWaleckiRightVertex] using hiy⟩⟩
            · intro t ht
              rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
              cases t with
              | inl t =>
                  simp [tripleWaleckiExtensionVertex] at hi
              | inr t =>
                  cases t with
                  | inl b' =>
                      have hiparsed : finToZModThree i = x ∧ b' = b := by
                        simpa [tripleWaleckiExtensionVertex, tripleWaleckiRightVertex] using hi
                      have hb' : b' = b := hiparsed.2
                      subst b'
                      rfl
                  | inr q =>
                      rcases q with ⟨e, p⟩
                      exact False.elim (hxy (tripleWaleckiCross_two_same_right_equal F hi hj))
          · rcases existsUnique_tripleWaleckiCross_right_right F x b y b' hbb'
              with ⟨q, hq, hquniq⟩
            refine ⟨Sum.inr (Sum.inr q), hq, ?_⟩
            intro t ht
            cases t with
            | inl t =>
                rcases ht.1 with ⟨i, hi⟩
                simp [tripleWaleckiExtensionVertex] at hi
            | inr t =>
                cases t with
                | inl b'' =>
                    rcases ht with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
                    have hiparsed : finToZModThree i = x ∧ b'' = b := by
                      simpa [tripleWaleckiExtensionVertex, tripleWaleckiRightVertex] using hi
                    have hjparsed : finToZModThree j = y ∧ b'' = b' := by
                      simpa [tripleWaleckiExtensionVertex, tripleWaleckiRightVertex] using hj
                    have hb : b'' = b := hiparsed.2
                    have hb' : b'' = b' := hjparsed.2
                    exact False.elim (hbb' (hb.symm.trans hb'))
                | inr q' =>
                    apply congrArg (fun r => Sum.inr (Sum.inr r))
                    exact hquniq q' ht

/-- Expand every point of the right side of a Walecki extension to a triple.
The source's Lemma 8 is this construction with the explicit Walecki
factorization on an even collection of right triples. -/
noncomputable def tripleWaleckiExtension
    (S : SteinerTripleSystem (ZMod 3 × α)) (F : OneFactorization β α) :
    SteinerTripleSystem (tripleWaleckiCarrier (α := α) (β := β)) where
  Triangle := S.Triangle ⊕ (β ⊕ (OffDiagonalPair β × (ZMod 3 × ZMod 3)))
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := tripleWaleckiExtensionVertex F S
  vertex_injective := tripleWaleckiExtensionVertex_injective F S
  pair_covered_once := tripleWaleckiExtension_pair_covered_once F S

end TripleWaleckiExtension

section FederSubiLemmaEight

variable {f : ℕ} [NeZero f]

private theorem card_tripleWaleckiLemmaEightSource :
    Fintype.card (ZMod 3 × ZMod f) = 3 * f := by
  rw [Fintype.card_prod, ZMod.card, ZMod.card]

private theorem card_tripleWaleckiLemmaEightCarrier :
    Fintype.card (tripleWaleckiCarrier (α := ZMod f) (β := Option (ZMod f))) =
      2 * (3 * f) + 3 := by
  simp only [Fintype.card_sum, Fintype.card_prod, ZMod.card, Fintype.card_option]
  omega

/-- Feder--Subi Lemma 8 with finite labels. If `f` is odd and an `STS(3f)`
is given, choose the `f+1` right triples and use Walecki's `f` factorization
to obtain an `STS(2(3f)+3)`. -/
noncomputable def twoTimesTriplePlusThreeFin (hf : Odd f)
    (S : SteinerTripleSystem (Fin (3 * f))) :
    SteinerTripleSystem (Fin (2 * (3 * f) + 3)) :=
  let sourceRelabel : ZMod 3 × ZMod f ≃ Fin (3 * f) :=
    Fintype.equivFinOfCardEq card_tripleWaleckiLemmaEightSource
  SteinerTripleSystem.map
    (Fintype.equivFinOfCardEq card_tripleWaleckiLemmaEightCarrier)
    (tripleWaleckiExtension (α := ZMod f) (β := Option (ZMod f))
      (SteinerTripleSystem.map sourceRelabel.symm S) (Walecki.oneFactorization hf))

end FederSubiLemmaEight

section FederSubiKirkmanInduction

/-- The source calls these cardinalities "good". -/
private def KirkmanGood (n : ℕ) : Prop := n % 6 = 1 ∨ n % 6 = 3

private theorem odd_of_KirkmanGood {n : ℕ} (hn : KirkmanGood n) : Odd n := by
  refine ⟨n / 2, ?_⟩
  unfold KirkmanGood at hn
  omega

/-- Feder--Subi Lemma 9: repeatedly applying the explicit preceding
constructions yields a Steiner triple system at every cardinality congruent
to `1` or `3` modulo six.  The residue split is the source's induction,
written modulo 36 so that every recursive cardinality is visibly smaller. -/
theorem exists_steinerTripleSystem_of_KirkmanGood (n : ℕ) (hn : KirkmanGood n) :
    Nonempty (SteinerTripleSystem (Fin n)) := by
  classical
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hn_one : n = 1
      · subst n
        exact ⟨SteinerTripleSystem.finOne⟩
      by_cases hn_three : n = 3
      · subst n
        exact ⟨SteinerTripleSystem.finThree⟩
      by_cases hcentered : n % 36 = 1 ∨ n % 36 = 25
      · let c := (n + 2) / 3
        have hc_lt : c < n := by
          dsimp [c]
          rcases hcentered with h | h <;> omega
        have hc_good : KirkmanGood c := by
          unfold KirkmanGood
          rcases hcentered with h | h <;> dsimp [c] <;> omega
        rcases ih c hc_lt hc_good with ⟨S⟩
        have hc_pos : 0 < c := by
          dsimp [c]
          omega
        letI : NeZero (c - 1) := ⟨by omega⟩
        have hc_eq : (c - 1) + 1 = c :=
          Nat.sub_add_cancel (Nat.succ_le_iff.mpr hc_pos)
        have S' : SteinerTripleSystem (Fin ((c - 1) + 1)) := by
          exact SteinerTripleSystem.map (finCongr hc_eq.symm) S
        have out := centeredTriplingFinOfFin (m := c - 1) S'
        have hout : 3 * ((c - 1) + 1) - 2 = n := by
          rw [hc_eq]
          rcases hcentered with h | h <;> dsimp [c] <;> omega
        exact ⟨SteinerTripleSystem.map (finCongr hout) out⟩
      by_cases hwalecki : n % 36 = 3 ∨ n % 36 = 7 ∨ n % 36 = 15 ∨
          n % 36 = 19 ∨ n % 36 = 27 ∨ n % 36 = 31
      · let m := (n - 1) / 2
        have hm_lt : m < n := by
          dsimp [m]
          rcases hwalecki with h | h | h | h | h | h <;> omega
        have hm_good : KirkmanGood m := by
          unfold KirkmanGood
          rcases hwalecki with h | h | h | h | h | h <;> dsimp [m] <;> omega
        rcases ih m hm_lt hm_good with ⟨S⟩
        letI : NeZero m := ⟨by
          dsimp [m]
          omega⟩
        have hm_odd : Odd m := odd_of_KirkmanGood hm_good
        have out := waleckiDoublePlusOneFinOfFin (m := m) hm_odd S
        have hout : 2 * m + 1 = n := by
          rcases hwalecki with h | h | h | h | h | h <;> dsimp [m] <;> omega
        exact ⟨SteinerTripleSystem.map (finCongr hout) out⟩
      by_cases hsix : n % 36 = 13
      · let d := (n + 5) / 6
        let g := (d - 1) / 2
        have hd_lt : d < n := by
          dsimp [d]
          omega
        have hd_good : KirkmanGood d := by
          unfold KirkmanGood
          dsimp [d]
          omega
        rcases ih d hd_lt hd_good with ⟨S⟩
        have hg_pos : 0 < g := by
          dsimp [g, d]
          omega
        letI : NeZero g := ⟨by omega⟩
        have S' : SteinerTripleSystem (Fin (2 * g + 1)) := by
          have hd : d = 6 * (n / 36) + 3 := by
            dsimp [d]
            omega
          have hg : g = 3 * (n / 36) + 1 := by
            dsimp [g]
            rw [hd]
            omega
          have hsource : d = 2 * g + 1 := by
            rw [hd, hg]
            omega
          exact SteinerTripleSystem.map (finCongr hsource) S
        have out := sixTimesMinusFiveFinOfFin (g := g) S'
        have hout : 6 * (2 * g + 1) - 5 = n := by
          have hd : d = 6 * (n / 36) + 3 := by
            dsimp [d]
            omega
          have hg : g = 3 * (n / 36) + 1 := by
            dsimp [g]
            rw [hd]
            omega
          rw [hg]
          omega
        exact ⟨SteinerTripleSystem.map (finCongr hout) out⟩
      by_cases htripling : n % 36 = 9 ∨ n % 36 = 21
      · let b := n / 3
        have hb_lt : b < n := by
          dsimp [b]
          rcases htripling with h | h <;> omega
        have hb_good : KirkmanGood b := by
          unfold KirkmanGood
          rcases htripling with h | h <;> dsimp [b] <;> omega
        rcases ih b hb_lt hb_good with ⟨S⟩
        letI : NeZero b := ⟨by
          dsimp [b]
          omega⟩
        have out := triplingFinOfFin (m := b) S
        have hout : 3 * b = n := by
          rcases htripling with h | h <;> dsimp [b] <;> omega
        exact ⟨SteinerTripleSystem.map (finCongr hout) out⟩
      by_cases hlemmaEight : n % 36 = 33
      · let f := (n - 3) / 6
        have hf_lt : 3 * f < n := by
          dsimp [f]
          omega
        have hf_source_good : KirkmanGood (3 * f) := by
          unfold KirkmanGood
          dsimp [f]
          omega
        rcases ih (3 * f) hf_lt hf_source_good with ⟨S⟩
        have hf_pos : 0 < f := by
          dsimp [f]
          omega
        letI : NeZero f := ⟨by omega⟩
        have hf_odd : Odd f := by
          refine ⟨f / 2, ?_⟩
          dsimp [f]
          omega
        have out := twoTimesTriplePlusThreeFin (f := f) hf_odd S
        have hout : 2 * (3 * f) + 3 = n := by
          dsimp [f]
          omega
        exact ⟨SteinerTripleSystem.map (finCongr hout) out⟩
      exfalso
      unfold KirkmanGood at hn
      have hmod_lt : n % 36 < 36 := Nat.mod_lt _ (by omega)
      push_neg at hcentered hwalecki
      omega

/-- The Kirkman existence theorem in the source's standard congruence form. -/
theorem steinerTripleSystem_exists_of_modSix (n : ℕ)
    (hn : n % 6 = 1 ∨ n % 6 = 3) :
    Nonempty (SteinerTripleSystem (Fin n)) :=
  exists_steinerTripleSystem_of_KirkmanGood n hn

end FederSubiKirkmanInduction

end SteinerTripleSystem

end Combinatorics
end Foundations
end AppliedModelingLib
