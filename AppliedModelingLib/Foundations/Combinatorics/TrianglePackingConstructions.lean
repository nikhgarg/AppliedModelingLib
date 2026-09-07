import AppliedModelingLib.Foundations.Combinatorics.TrianglePacking
import AppliedModelingLib.Foundations.Combinatorics.SteinerTripleConstructions
import AppliedModelingLib.Foundations.Combinatorics.Walecki
import AppliedModelingLib.Foundations.Graph.AlternatingPairingOrientation

/-!
# Constructors for finite triangle packings

These constructions retain the exact edge-disjoint triangle data needed for
near-decompositions, where a Steiner triple system would be too restrictive.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Combinatorics

namespace TrianglePacking

open SteinerTripleSystem

section Transversal

variable {m : ℕ} [NeZero m]

/-- The `m²` transversal triangles between three groups of size `m` from the
Feder--Subi tripling construction.  It covers every pair in distinct groups
exactly once and deliberately contains no within-group edge. -/
noncomputable def transversal (m : ℕ) [NeZero m] :
    TrianglePacking (Fin 3 × ZMod m) where
  Triangle := ZMod m × ZMod m
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := triplingCrossVertex
  vertex_injective := triplingCrossVertex_injective
  pair_covered_at_most_once := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hxy p q hp_a hp_b hq_a hq_b
    by_cases hab : a = b
    · have hip : hp_a.choose = a :=
        triplingCrossVertex_index_eq_fst hp_a.choose_spec
      have hjp : hp_b.choose = b :=
        triplingCrossVertex_index_eq_fst hp_b.choose_spec
      have hiq : hq_a.choose = a :=
        triplingCrossVertex_index_eq_fst hq_a.choose_spec
      have hjq : hq_b.choose = b :=
        triplingCrossVertex_index_eq_fst hq_b.choose_spec
      subst b
      have hpij : hp_a.choose = hp_b.choose := hip.trans hjp.symm
      have hqij : hq_a.choose = hq_b.choose := hiq.trans hjq.symm
      exact False.elim (hxy (by
        apply Prod.ext
        · rfl
        · calc
            x = (triplingCrossVertex p (hp_a.choose)).2 :=
              congrArg Prod.snd hp_a.choose_spec.symm
            _ = (triplingCrossVertex p (hp_b.choose)).2 := by rw [hpij]
            _ = y := congrArg Prod.snd hp_b.choose_spec))
    · rcases existsUnique_triplingCross_of_distinct a b x y hab with ⟨r, hr, hruniq⟩
      exact (hruniq p ⟨hp_a, hp_b⟩).trans (hruniq q ⟨hq_a, hq_b⟩).symm

end Transversal

section SixPointGroups

/-- A fixed relabeling of Walecki's six-point carrier to `ZMod 6`. -/
noncomputable def optionZModFiveEquivZModSix : Option (ZMod 5) ≃ ZMod 6 := by
  let e1 : Option (ZMod 5) ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by norm_num [Fintype.card_option, ZMod.card])
  let e2 : ZMod 6 ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by norm_num [ZMod.card])
  exact e1.trans e2.symm

/-- The five Walecki perfect matchings of a group of six points, indexed by
the five residual vertices in Feder--Subi's `n = 6x + 5` construction. -/
noncomputable def sixPointGroupFactorization :
    OneFactorization (ZMod 6) (ZMod 5) := by
  letI : NeZero 5 := ⟨by decide⟩
  exact OneFactorization.map optionZModFiveEquivZModSix
    (Walecki.oneFactorization (m := 5) (by decide))

/-- One representative of each edge of the `r`th six-point matching.  The
strict comparison of the two residue representatives prevents the two
orientations of an involutive matching edge from creating duplicate
triangles. -/
private abbrev SixPointMatchingRepresentative (r : ZMod 5) :=
  {x : ZMod 6 // x.val < ((sixPointGroupFactorization.matching r).perm x).val}

private noncomputable def sixPointMatchingRepresentative (r : ZMod 5) (x : ZMod 6) :
    SixPointMatchingRepresentative r :=
  if hx : x.val < ((sixPointGroupFactorization.matching r).perm x).val then
    ⟨x, hx⟩
  else
    ⟨(sixPointGroupFactorization.matching r).perm x, by
      have hne : (sixPointGroupFactorization.matching r).perm x ≠ x :=
        (sixPointGroupFactorization.matching r).apply_ne x
      have hvalne : ((sixPointGroupFactorization.matching r).perm x).val ≠ x.val := by
        intro h
        apply hne
        exact ZMod.val_injective 6 h
      rw [(sixPointGroupFactorization.matching r).apply_apply]
      omega⟩

private theorem sixPointMatchingRepresentative_eq_self
    (r : ZMod 5) (x : SixPointMatchingRepresentative r) :
    sixPointMatchingRepresentative r x.1 = x := by
  apply Subtype.ext
  simp [sixPointMatchingRepresentative, x.2]

private theorem sixPointMatchingRepresentative_perm_eq_self
    (r : ZMod 5) (x : SixPointMatchingRepresentative r) :
    sixPointMatchingRepresentative r ((sixPointGroupFactorization.matching r).perm x.1) = x := by
  apply Subtype.ext
  have hnot : ¬ ((sixPointGroupFactorization.matching r).perm x.1).val <
      ((sixPointGroupFactorization.matching r).perm
        ((sixPointGroupFactorization.matching r).perm x.1)).val := by
    rw [(sixPointGroupFactorization.matching r).apply_apply]
    omega
  rw [(sixPointGroupFactorization.matching r).apply_apply] at hnot
  simp [sixPointMatchingRepresentative, hnot,
    (sixPointGroupFactorization.matching r).apply_apply]

private theorem sixPointMatchingRepresentative_endpoints
    (r : ZMod 5) (x : ZMod 6) :
    x = (sixPointMatchingRepresentative r x).1 ∨
      x = (sixPointGroupFactorization.matching r).perm
        (sixPointMatchingRepresentative r x).1 := by
  unfold sixPointMatchingRepresentative
  split
  · exact Or.inl rfl
  · rename_i hx
    exact Or.inr ((sixPointGroupFactorization.matching r).apply_apply x).symm

/-- The canonical representative is determined by either endpoint of its
matching edge. -/
private theorem sixPointMatchingRepresentative_eq_of_endpoint
    (r : ZMod 5) (u : SixPointMatchingRepresentative r) (x : ZMod 6)
    (hx : x = u.1 ∨ x = (sixPointGroupFactorization.matching r).perm u.1) :
    sixPointMatchingRepresentative r x = u := by
  rcases hx with hx | hx
  · subst x
    exact sixPointMatchingRepresentative_eq_self r u
  · subst x
    exact sixPointMatchingRepresentative_perm_eq_self r u

end SixPointGroups

section CenterRemovedSteiner

open AppliedModelingLib.Foundations.Graph

variable {β : Type} [Fintype β] [DecidableEq β]

private theorem exists_third_index (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | decide

private noncomputable def thirdIndex (i j : Fin 3) (hij : i ≠ j) : Fin 3 :=
  (exists_third_index i j hij).choose

private theorem thirdIndex_ne_left (i j : Fin 3) (hij : i ≠ j) :
    thirdIndex i j hij ≠ i :=
  (exists_third_index i j hij).choose_spec.1

private theorem thirdIndex_ne_right (i j : Fin 3) (hij : i ≠ j) :
    thirdIndex i j hij ≠ j :=
  (exists_third_index i j hij).choose_spec.2

private theorem finThree_third_unique (i j k l : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hli : l ≠ i) (hlk : l ≠ k) : l = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp at hij hik hjk hli hlk ⊢

private noncomputable def centerTriangle
    (S : SteinerTripleSystem (Option β)) (x : β) : S.Triangle :=
  S.triangleOfPair none (some x) (by simp)

private noncomputable def centerNoneIndex
    (S : SteinerTripleSystem (Option β)) (x : β) : Fin 3 :=
  (S.pair_mem_triangleOfPair none (some x) (by simp)).1.choose

private noncomputable def centerSomeIndex
    (S : SteinerTripleSystem (Option β)) (x : β) : Fin 3 :=
  (S.pair_mem_triangleOfPair none (some x) (by simp)).2.choose

private theorem centerNoneIndex_spec
    (S : SteinerTripleSystem (Option β)) (x : β) :
    S.vertex (centerTriangle S x) (centerNoneIndex S x) = none :=
  (S.pair_mem_triangleOfPair none (some x) (by simp)).1.choose_spec

private theorem centerSomeIndex_spec
    (S : SteinerTripleSystem (Option β)) (x : β) :
    S.vertex (centerTriangle S x) (centerSomeIndex S x) = some x :=
  (S.pair_mem_triangleOfPair none (some x) (by simp)).2.choose_spec

private theorem centerIndices_ne
    (S : SteinerTripleSystem (Option β)) (x : β) :
    centerNoneIndex S x ≠ centerSomeIndex S x := by
  intro h
  have hnone_some : (none : Option β) = some x := by
    calc
      none = S.vertex (centerTriangle S x) (centerNoneIndex S x) :=
        (centerNoneIndex_spec S x).symm
      _ = S.vertex (centerTriangle S x) (centerSomeIndex S x) := by rw [h]
      _ = some x := centerSomeIndex_spec S x
  simp at hnone_some

private theorem exists_center_partner
    (S : SteinerTripleSystem (Option β)) (x : β) :
    ∃ y : β,
      S.vertex (centerTriangle S x)
        (thirdIndex (centerNoneIndex S x) (centerSomeIndex S x) (centerIndices_ne S x)) = some y := by
  let i := centerNoneIndex S x
  let j := centerSomeIndex S x
  let k := thirdIndex i j (centerIndices_ne S x)
  cases hk : S.vertex (centerTriangle S x) k with
  | none =>
      exact False.elim ((thirdIndex_ne_left i j (centerIndices_ne S x))
        (S.vertex_injective (centerTriangle S x) (by
          calc
            S.vertex (centerTriangle S x) k = none := hk
            _ = S.vertex (centerTriangle S x) i := (centerNoneIndex_spec S x).symm)))
  | some y => exact ⟨y, by simpa [i, j, k] using hk⟩

private noncomputable def centerPartner
    (S : SteinerTripleSystem (Option β)) (x : β) : β :=
  (exists_center_partner S x).choose

private theorem centerPartner_spec
    (S : SteinerTripleSystem (Option β)) (x : β) :
    S.vertex (centerTriangle S x)
      (thirdIndex (centerNoneIndex S x) (centerSomeIndex S x) (centerIndices_ne S x)) =
        some (centerPartner S x) :=
  (exists_center_partner S x).choose_spec

private theorem centerPartner_ne
    (S : SteinerTripleSystem (Option β)) (x : β) : centerPartner S x ≠ x := by
  intro h
  apply (thirdIndex_ne_right (centerNoneIndex S x) (centerSomeIndex S x)
    (centerIndices_ne S x))
  apply S.vertex_injective (centerTriangle S x)
  calc
    S.vertex (centerTriangle S x)
        (thirdIndex (centerNoneIndex S x) (centerSomeIndex S x) (centerIndices_ne S x)) =
        some (centerPartner S x) := centerPartner_spec S x
    _ = some x := by rw [h]
    _ = S.vertex (centerTriangle S x) (centerSomeIndex S x) :=
      (centerSomeIndex_spec S x).symm

private theorem centerPartner_apply_apply
    (S : SteinerTripleSystem (Option β)) (x : β) :
    centerPartner S (centerPartner S x) = x := by
  let i := centerNoneIndex S x
  let j := centerSomeIndex S x
  let k := thirdIndex i j (centerIndices_ne S x)
  let y := centerPartner S x
  have htriangle : centerTriangle S x = centerTriangle S y := by
    apply S.eq_triangleOfPair_of_contains none (some y) (by simp)
      (centerTriangle S x)
    · exact ⟨i, centerNoneIndex_spec S x⟩
    · exact ⟨k, centerPartner_spec S x⟩
  let i' := centerNoneIndex S y
  let j' := centerSomeIndex S y
  let k' := thirdIndex i' j' (centerIndices_ne S y)
  have hi' : S.vertex (centerTriangle S x) i' = none := by
    rw [htriangle]
    exact centerNoneIndex_spec S y
  have hj' : S.vertex (centerTriangle S x) j' = some y := by
    rw [htriangle]
    exact centerSomeIndex_spec S y
  have hk' : S.vertex (centerTriangle S x) k' = some (centerPartner S y) := by
    rw [htriangle]
    exact centerPartner_spec S y
  have hii' : i' = i := S.vertex_injective (centerTriangle S x)
    (hi'.trans (centerNoneIndex_spec S x).symm)
  have hjk : j' = k := S.vertex_injective (centerTriangle S x)
    (hj'.trans (centerPartner_spec S x).symm)
  have hk'i : k' ≠ i := by
    rw [← hii']
    exact thirdIndex_ne_left i' j' (centerIndices_ne S y)
  have hk'k : k' ≠ k := by
    rw [← hjk]
    exact thirdIndex_ne_right i' j' (centerIndices_ne S y)
  have hk'j : k' = j := finThree_third_unique i j k k'
    (centerIndices_ne S x)
    ((thirdIndex_ne_left i j (centerIndices_ne S x)).symm)
    ((thirdIndex_ne_right i j (centerIndices_ne S x)).symm)
    hk'i hk'k
  have hsome : some (centerPartner S y) = some x := by
    calc
      some (centerPartner S y) = S.vertex (centerTriangle S x) k' := hk'.symm
      _ = S.vertex (centerTriangle S x) j := by rw [hk'j]
      _ = some x := centerSomeIndex_spec S x
  exact Option.some.inj hsome

private noncomputable def centerLeavePairing
    (S : SteinerTripleSystem (Option β)) : EvenPairing β where
  perm :=
    { toFun := centerPartner S
      invFun := centerPartner S
      left_inv := centerPartner_apply_apply S
      right_inv := centerPartner_apply_apply S }
  apply_apply := centerPartner_apply_apply S
  apply_ne := centerPartner_ne S

private theorem centerLeavePairing_apply
    (S : SteinerTripleSystem (Option β)) (x : β) :
    (centerLeavePairing S).perm x = centerPartner S x := rfl

private noncomputable def optionGetOfNeNone (z : Option β) (h : z ≠ none) : β :=
  match z with
  | some x => x
  | none => False.elim (h rfl)

private theorem some_optionGetOfNeNone (z : Option β) (h : z ≠ none) :
    some (optionGetOfNeNone z h) = z := by
  cases z <;> simp [optionGetOfNeNone] at h ⊢

private abbrev CenterFreeTriangle (S : SteinerTripleSystem (Option β)) :=
  {t : S.Triangle // ∀ i : Fin 3, S.vertex t i ≠ none}

private noncomputable def centerFreeVertex (S : SteinerTripleSystem (Option β))
    (t : CenterFreeTriangle S) (i : Fin 3) : β :=
  optionGetOfNeNone (S.vertex t.1 i) (t.2 i)

private theorem centerFreeVertex_source
    (S : SteinerTripleSystem (Option β)) (t : CenterFreeTriangle S) (i : Fin 3) :
    some (centerFreeVertex S t i) = S.vertex t.1 i :=
  some_optionGetOfNeNone _ _

private theorem centerFreeVertex_injective
    (S : SteinerTripleSystem (Option β)) (t : CenterFreeTriangle S) :
    Function.Injective (centerFreeVertex S t) := by
  intro i j hij
  apply S.vertex_injective t.1
  calc
    S.vertex t.1 i = some (centerFreeVertex S t i) := (centerFreeVertex_source S t i).symm
    _ = some (centerFreeVertex S t j) := by rw [hij]
    _ = S.vertex t.1 j := centerFreeVertex_source S t j

private noncomputable def centerRemovedPacking
    (S : SteinerTripleSystem (Option β)) : TrianglePacking β where
  Triangle := CenterFreeTriangle S
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := centerFreeVertex S
  vertex_injective := centerFreeVertex_injective S
  pair_covered_at_most_once := by
    intro x y hxy t u htx hty hux huy
    rcases htx with ⟨i, hi⟩
    rcases hty with ⟨j, hj⟩
    rcases hux with ⟨k, hk⟩
    rcases huy with ⟨l, hl⟩
    apply Subtype.ext
    exact (S.eq_triangleOfPair_of_contains (some x) (some y) (by simpa using hxy) t.1
      ⟨i, by
        calc
          S.vertex t.1 i = some (centerFreeVertex S t i) :=
            (centerFreeVertex_source S t i).symm
          _ = some x := by rw [hi]⟩
      ⟨j, by
        calc
          S.vertex t.1 j = some (centerFreeVertex S t j) :=
            (centerFreeVertex_source S t j).symm
          _ = some y := by rw [hj]⟩).trans
      (S.eq_triangleOfPair_of_contains (some x) (some y) (by simpa using hxy) u.1
        ⟨k, by
          calc
            S.vertex u.1 k = some (centerFreeVertex S u k) :=
              (centerFreeVertex_source S u k).symm
            _ = some x := by rw [hk]⟩
        ⟨l, by
          calc
            S.vertex u.1 l = some (centerFreeVertex S u l) :=
              (centerFreeVertex_source S u l).symm
            _ = some y := by rw [hl]⟩).symm

private theorem eq_centerPartner_of_mem_centerTriangle
    (S : SteinerTripleSystem (Option β)) (x z : β) (hxz : x ≠ z)
    (hz : ∃ l : Fin 3, S.vertex (centerTriangle S x) l = some z) :
    z = centerPartner S x := by
  rcases hz with ⟨l, hl⟩
  let i := centerNoneIndex S x
  let j := centerSomeIndex S x
  let k := thirdIndex i j (centerIndices_ne S x)
  have hli : l ≠ i := by
    intro h
    have hnone_some : (none : Option β) = some z := by
      calc
        none = S.vertex (centerTriangle S x) i := (centerNoneIndex_spec S x).symm
        _ = S.vertex (centerTriangle S x) l := by rw [h]
        _ = some z := hl
    simp at hnone_some
  have hlj : l ≠ j := by
    intro h
    apply hxz
    apply Option.some.inj
    calc
      some x = S.vertex (centerTriangle S x) j := (centerSomeIndex_spec S x).symm
      _ = S.vertex (centerTriangle S x) l := by rw [h]
      _ = some z := hl
  have hlk : l = k := finThree_third_unique i k j l
    ((thirdIndex_ne_left i j (centerIndices_ne S x)).symm)
    (centerIndices_ne S x)
    (thirdIndex_ne_right i j (centerIndices_ne S x))
    hli hlj
  apply Option.some.inj
  calc
    some z = S.vertex (centerTriangle S x) l := hl.symm
    _ = S.vertex (centerTriangle S x) k := by rw [hlk]
    _ = some (centerPartner S x) := centerPartner_spec S x

private theorem centerRemovedPacking_covers_iff
    (S : SteinerTripleSystem (Option β)) (x y : β) (hxy : x ≠ y) :
    (centerRemovedPacking S).CoversPair x y ↔ centerPartner S x ≠ y := by
  constructor
  · rintro ⟨q, ⟨i, hi⟩, ⟨j, hj⟩⟩ hpartner
    change centerFreeVertex S q i = x at hi
    change centerFreeVertex S q j = y at hj
    have hqxy : q.1 = centerTriangle S x := by
      have hpair : q.1 = S.triangleOfPair (some x) (some y) (by simpa using hxy) :=
        S.eq_triangleOfPair_of_contains (some x) (some y) (by simpa using hxy) q.1
          ⟨i, by
            calc
              S.vertex q.1 i = some (centerFreeVertex S q i) :=
                (centerFreeVertex_source S q i).symm
              _ = some x := by rw [hi]⟩
          ⟨j, by
            calc
              S.vertex q.1 j = some (centerFreeVertex S q j) :=
                (centerFreeVertex_source S q j).symm
              _ = some y := by rw [hj]⟩
      have hcenter : centerTriangle S x =
          S.triangleOfPair (some x) (some y) (by simpa using hxy) := by
        apply S.eq_triangleOfPair_of_contains (some x) (some y) (by simpa using hxy)
          (centerTriangle S x)
        · exact ⟨centerSomeIndex S x, centerSomeIndex_spec S x⟩
        · refine ⟨thirdIndex (centerNoneIndex S x) (centerSomeIndex S x) (centerIndices_ne S x), ?_⟩
          simpa [hpartner] using centerPartner_spec S x
      exact hpair.trans hcenter.symm
    apply q.2 (centerNoneIndex S x)
    rw [hqxy]
    exact centerNoneIndex_spec S x
  · intro hpartner
    let t := S.triangleOfPair (some x) (some y) (by simpa using hxy)
    have hfree : ∀ i : Fin 3, S.vertex t i ≠ none := by
      intro i hinone
      have htcenter : t = centerTriangle S x := by
        apply S.eq_triangleOfPair_of_contains none (some x) (by simp) t
        · exact ⟨i, hinone⟩
        · rcases S.pair_mem_triangleOfPair (some x) (some y) (by simpa using hxy) with
            ⟨⟨ix, hix⟩, _⟩
          exact ⟨ix, by simpa [t] using hix⟩
      have hycenter : ∃ l : Fin 3, S.vertex (centerTriangle S x) l = some y := by
        rcases S.pair_mem_triangleOfPair (some x) (some y) (by simpa using hxy) with
          ⟨_, ⟨iy, hiy⟩⟩
        exact ⟨iy, by
          rw [← htcenter]
          simpa [t] using hiy⟩
      apply hpartner
      exact (eq_centerPartner_of_mem_centerTriangle S x y hxy hycenter).symm
    refine ⟨⟨t, hfree⟩, ?_, ?_⟩
    · rcases S.pair_mem_triangleOfPair (some x) (some y) (by simpa using hxy) with
        ⟨⟨i, hi⟩, _⟩
      refine ⟨i, ?_⟩
      apply Option.some.inj
      calc
        some (centerFreeVertex S ⟨t, hfree⟩ i) = S.vertex t i :=
          centerFreeVertex_source S ⟨t, hfree⟩ i
        _ = some x := by simpa [t] using hi
    · rcases S.pair_mem_triangleOfPair (some x) (some y) (by simpa using hxy) with
        ⟨_, ⟨j, hj⟩⟩
      refine ⟨j, ?_⟩
      apply Option.some.inj
      calc
        some (centerFreeVertex S ⟨t, hfree⟩ j) = S.vertex t j :=
          centerFreeVertex_source S ⟨t, hfree⟩ j
        _ = some y := by simpa [t] using hj

/-- Removing the distinguished point of an STS gives a triangle packing whose
only leave is the perfect matching induced by that point. -/
noncomputable def centerRemovedWithMatchingLeave
    (S : SteinerTripleSystem (Option β)) : TrianglePacking.WithMatchingLeave β where
  packing := centerRemovedPacking S
  matching := centerLeavePairing S
  coversPair_iff := fun x y hxy => by
    change (centerRemovedPacking S).CoversPair x y ↔ (centerLeavePairing S).perm x ≠ y
    rw [centerLeavePairing_apply]
    exact centerRemovedPacking_covers_iff S x y hxy

end CenterRemovedSteiner

section TripleRemovedSteiner

open AppliedModelingLib.Foundations.Graph

variable {β : Type} [Fintype β] [DecidableEq β]

/-- A source Steiner triple system with one displayed all-centre triangle.
Deleting that triangle is the macro step in Feder--Subi's final residue
construction. -/
private abbrev CenteredTripleSystem (β : Type) [Fintype β] [DecidableEq β] :=
  { S : SteinerTripleSystem (Fin 3 ⊕ β) //
    ∃ T : S.Triangle, ∀ i : Fin 3, S.vertex T i = Sum.inl i }

private noncomputable def tripleCenterTriangle
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) : S.Triangle :=
  S.triangleOfPair (Sum.inl i) (Sum.inr x) (by simp)

private noncomputable def tripleCenterIndex
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) : Fin 3 :=
  (S.pair_mem_triangleOfPair (Sum.inl i) (Sum.inr x) (by simp)).1.choose

private noncomputable def triplePointIndex
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) : Fin 3 :=
  (S.pair_mem_triangleOfPair (Sum.inl i) (Sum.inr x) (by simp)).2.choose

private theorem tripleCenterIndex_spec
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) :
    S.vertex (tripleCenterTriangle S i x) (tripleCenterIndex S i x) = Sum.inl i :=
  (S.pair_mem_triangleOfPair (Sum.inl i) (Sum.inr x) (by simp)).1.choose_spec

private theorem triplePointIndex_spec
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) :
    S.vertex (tripleCenterTriangle S i x) (triplePointIndex S i x) = Sum.inr x :=
  (S.pair_mem_triangleOfPair (Sum.inl i) (Sum.inr x) (by simp)).2.choose_spec

private theorem tripleCenterPointIndices_ne
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) :
    tripleCenterIndex S i x ≠ triplePointIndex S i x := by
  intro h
  have hleft_right : (Sum.inl i : Fin 3 ⊕ β) = Sum.inr x := by
    calc
      Sum.inl i = S.vertex (tripleCenterTriangle S i x) (tripleCenterIndex S i x) :=
        (tripleCenterIndex_spec S i x).symm
      _ = S.vertex (tripleCenterTriangle S i x) (triplePointIndex S i x) := by rw [h]
      _ = Sum.inr x := triplePointIndex_spec S i x
  simp at hleft_right

private noncomputable def tripleThirdIndex
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) : Fin 3 :=
  thirdIndex (tripleCenterIndex S i x) (triplePointIndex S i x)
    (tripleCenterPointIndices_ne S i x)

private theorem tripleThirdIndex_ne_center
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) :
    tripleThirdIndex S i x ≠ tripleCenterIndex S i x :=
  thirdIndex_ne_left _ _ _

private theorem tripleThirdIndex_ne_point
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (i : Fin 3) (x : β) :
    tripleThirdIndex S i x ≠ triplePointIndex S i x :=
  thirdIndex_ne_right _ _ _

private theorem tripleThird_is_right
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i : Fin 3) (x : β) :
    ∃ y : β, S.vertex (tripleCenterTriangle S i x) (tripleThirdIndex S i x) = Sum.inr y := by
  cases hthird : S.vertex (tripleCenterTriangle S i x) (tripleThirdIndex S i x) with
  | inr y => exact ⟨y, rfl⟩
  | inl j =>
      by_cases hij : i = j
      · subst j
        exact False.elim (tripleThirdIndex_ne_center S i x
          (S.vertex_injective (tripleCenterTriangle S i x) (by
            calc
              S.vertex (tripleCenterTriangle S i x) (tripleThirdIndex S i x) = Sum.inl i := hthird
              _ = S.vertex (tripleCenterTriangle S i x) (tripleCenterIndex S i x) :=
                (tripleCenterIndex_spec S i x).symm)))
      · have htriangle : tripleCenterTriangle S i x = T := by
          calc
            tripleCenterTriangle S i x =
                S.triangleOfPair (Sum.inl i) (Sum.inl j) (by simp [hij]) :=
              S.eq_triangleOfPair_of_contains (Sum.inl i) (Sum.inl j) (by simp [hij])
                (tripleCenterTriangle S i x)
                ⟨tripleCenterIndex S i x, tripleCenterIndex_spec S i x⟩
                ⟨tripleThirdIndex S i x, hthird⟩
            _ = T := (S.eq_triangleOfPair_of_contains (Sum.inl i) (Sum.inl j) (by simp [hij]) T
              ⟨i, hT i⟩ ⟨j, hT j⟩).symm
        have hleft_right : (Sum.inl (triplePointIndex S i x) : Fin 3 ⊕ β) = Sum.inr x := by
          calc
            Sum.inl (triplePointIndex S i x) = S.vertex T (triplePointIndex S i x) :=
              (hT _).symm
            _ = S.vertex (tripleCenterTriangle S i x) (triplePointIndex S i x) := by
              rw [htriangle]
            _ = Sum.inr x := triplePointIndex_spec S i x
        simp at hleft_right

private noncomputable def triplePartner
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i : Fin 3) (x : β) : β :=
  (tripleThird_is_right S T hT i x).choose

private theorem triplePartner_spec
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i : Fin 3) (x : β) :
    S.vertex (tripleCenterTriangle S i x) (tripleThirdIndex S i x) =
      Sum.inr (triplePartner S T hT i x) :=
  (tripleThird_is_right S T hT i x).choose_spec

private theorem triplePartner_ne
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i : Fin 3) (x : β) : triplePartner S T hT i x ≠ x := by
  intro h
  apply tripleThirdIndex_ne_point S i x
  apply S.vertex_injective (tripleCenterTriangle S i x)
  calc
    S.vertex (tripleCenterTriangle S i x) (tripleThirdIndex S i x) =
        Sum.inr (triplePartner S T hT i x) := triplePartner_spec S T hT i x
    _ = Sum.inr x := by rw [h]
    _ = S.vertex (tripleCenterTriangle S i x) (triplePointIndex S i x) :=
      (triplePointIndex_spec S i x).symm

private theorem triplePartner_apply_apply
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i : Fin 3) (x : β) :
    triplePartner S T hT i (triplePartner S T hT i x) = x := by
  let a := tripleCenterIndex S i x
  let b := triplePointIndex S i x
  let c := tripleThirdIndex S i x
  let y := triplePartner S T hT i x
  have htriangle : tripleCenterTriangle S i x = tripleCenterTriangle S i y := by
    apply S.eq_triangleOfPair_of_contains (Sum.inl i) (Sum.inr y) (by simp)
      (tripleCenterTriangle S i x)
    · exact ⟨a, tripleCenterIndex_spec S i x⟩
    · exact ⟨c, triplePartner_spec S T hT i x⟩
  let a' := tripleCenterIndex S i y
  let b' := triplePointIndex S i y
  let c' := tripleThirdIndex S i y
  have ha' : S.vertex (tripleCenterTriangle S i x) a' = Sum.inl i := by
    rw [htriangle]
    exact tripleCenterIndex_spec S i y
  have hb' : S.vertex (tripleCenterTriangle S i x) b' = Sum.inr y := by
    rw [htriangle]
    exact triplePointIndex_spec S i y
  have hc' : S.vertex (tripleCenterTriangle S i x) c' =
      Sum.inr (triplePartner S T hT i y) := by
    rw [htriangle]
    exact triplePartner_spec S T hT i y
  have haa' : a' = a := S.vertex_injective (tripleCenterTriangle S i x)
    (ha'.trans (tripleCenterIndex_spec S i x).symm)
  have hbc : b' = c := S.vertex_injective (tripleCenterTriangle S i x)
    (hb'.trans (triplePartner_spec S T hT i x).symm)
  have hc'a : c' ≠ a := by
    rw [← haa']
    exact tripleThirdIndex_ne_center S i y
  have hc'c : c' ≠ c := by
    rw [← hbc]
    exact tripleThirdIndex_ne_point S i y
  have hc'b : c' = b := finThree_third_unique a b c c'
    (tripleCenterPointIndices_ne S i x)
    ((tripleThirdIndex_ne_center S i x).symm)
    ((tripleThirdIndex_ne_point S i x).symm)
    hc'a hc'c
  apply Sum.inr.inj
  calc
    Sum.inr (triplePartner S T hT i y) = S.vertex (tripleCenterTriangle S i x) c' := hc'.symm
    _ = S.vertex (tripleCenterTriangle S i x) b := by rw [hc'b]
    _ = Sum.inr x := triplePointIndex_spec S i x

private noncomputable def tripleLeavePairing
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i : Fin 3) : EvenPairing β where
  perm :=
    { toFun := triplePartner S T hT i
      invFun := triplePartner S T hT i
      left_inv := triplePartner_apply_apply S T hT i
      right_inv := triplePartner_apply_apply S T hT i }
  apply_apply := triplePartner_apply_apply S T hT i
  apply_ne := triplePartner_ne S T hT i

private abbrev TripleFreeTriangle (S : SteinerTripleSystem (Fin 3 ⊕ β)) :=
  { t : S.Triangle // ∀ i : Fin 3, ∃ x : β, S.vertex t i = Sum.inr x }

private noncomputable def tripleFreeVertex
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (t : TripleFreeTriangle S) (i : Fin 3) : β :=
  (t.2 i).choose

private theorem tripleFreeVertex_source
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (t : TripleFreeTriangle S) (i : Fin 3) :
    S.vertex t.1 i = Sum.inr (tripleFreeVertex S t i) :=
  (t.2 i).choose_spec

private theorem tripleFreeVertex_injective
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (t : TripleFreeTriangle S) :
    Function.Injective (tripleFreeVertex S t) := by
  intro i j hij
  apply S.vertex_injective t.1
  calc
    S.vertex t.1 i = Sum.inr (tripleFreeVertex S t i) := tripleFreeVertex_source S t i
    _ = Sum.inr (tripleFreeVertex S t j) := by rw [hij]
    _ = S.vertex t.1 j := (tripleFreeVertex_source S t j).symm

private noncomputable def tripleRemovedPacking
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) : TrianglePacking β where
  Triangle := TripleFreeTriangle S
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := tripleFreeVertex S
  vertex_injective := tripleFreeVertex_injective S
  pair_covered_at_most_once := by
    intro x y hxy t u htx hty hux huy
    rcases htx with ⟨i, hi⟩
    rcases hty with ⟨j, hj⟩
    rcases hux with ⟨k, hk⟩
    rcases huy with ⟨l, hl⟩
    apply Subtype.ext
    exact (S.eq_triangleOfPair_of_contains (Sum.inr x) (Sum.inr y) (by simpa using hxy) t.1
      ⟨i, by simpa [hi] using tripleFreeVertex_source S t i⟩
      ⟨j, by simpa [hj] using tripleFreeVertex_source S t j⟩).trans
      (S.eq_triangleOfPair_of_contains (Sum.inr x) (Sum.inr y) (by simpa using hxy) u.1
        ⟨k, by simpa [hk] using tripleFreeVertex_source S u k⟩
        ⟨l, by simpa [hl] using tripleFreeVertex_source S u l⟩).symm

private theorem triplePartner_eq_of_mem_centerTriangle
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i : Fin 3) (x z : β) (hxz : x ≠ z)
    (hz : ∃ l : Fin 3, S.vertex (tripleCenterTriangle S i x) l = Sum.inr z) :
    z = triplePartner S T hT i x := by
  rcases hz with ⟨l, hl⟩
  let a := tripleCenterIndex S i x
  let b := triplePointIndex S i x
  let c := tripleThirdIndex S i x
  have hla : l ≠ a := by
    intro h
    have hleft_right : (Sum.inl i : Fin 3 ⊕ β) = Sum.inr z := by
      calc
        Sum.inl i = S.vertex (tripleCenterTriangle S i x) a := (tripleCenterIndex_spec S i x).symm
        _ = S.vertex (tripleCenterTriangle S i x) l := by rw [h]
        _ = Sum.inr z := hl
    simp at hleft_right
  have hlb : l ≠ b := by
    intro h
    apply hxz
    apply Sum.inr.inj
    calc
      Sum.inr x = S.vertex (tripleCenterTriangle S i x) b := (triplePointIndex_spec S i x).symm
      _ = S.vertex (tripleCenterTriangle S i x) l := by rw [h]
      _ = Sum.inr z := hl
  have hlc : l = c := finThree_third_unique a c b l
    ((tripleThirdIndex_ne_center S i x).symm)
    (tripleCenterPointIndices_ne S i x)
    (tripleThirdIndex_ne_point S i x)
    hla hlb
  apply Sum.inr.inj
  calc
    Sum.inr z = S.vertex (tripleCenterTriangle S i x) l := hl.symm
    _ = S.vertex (tripleCenterTriangle S i x) c := by rw [hlc]
    _ = Sum.inr (triplePartner S T hT i x) := triplePartner_spec S T hT i x

private theorem tripleLeavePairings_disjoint
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (i j : Fin 3) (hij : i ≠ j) (x : β) :
    (tripleLeavePairing S T hT i).perm x ≠ (tripleLeavePairing S T hT j).perm x := by
  intro hpartner
  let y := triplePartner S T hT i x
  change triplePartner S T hT i x = triplePartner S T hT j x at hpartner
  have hpartnerj : triplePartner S T hT j x = y := by
    dsimp [y]
    exact hpartner.symm
  have hxy : x ≠ y := (triplePartner_ne S T hT i x).symm
  have htriangle : tripleCenterTriangle S i x = tripleCenterTriangle S j x := by
    calc
      tripleCenterTriangle S i x = S.triangleOfPair (Sum.inr x) (Sum.inr y) (by simpa using hxy) :=
        S.eq_triangleOfPair_of_contains (Sum.inr x) (Sum.inr y) (by simpa using hxy)
          (tripleCenterTriangle S i x)
          ⟨triplePointIndex S i x, triplePointIndex_spec S i x⟩
          ⟨tripleThirdIndex S i x, triplePartner_spec S T hT i x⟩
      _ = tripleCenterTriangle S j x :=
        (S.eq_triangleOfPair_of_contains (Sum.inr x) (Sum.inr y) (by simpa using hxy)
          (tripleCenterTriangle S j x)
          ⟨triplePointIndex S j x, triplePointIndex_spec S j x⟩
          ⟨tripleThirdIndex S j x, (triplePartner_spec S T hT j x).trans
            (congrArg Sum.inr hpartnerj)⟩).symm
  have htoT : tripleCenterTriangle S i x = T := by
    calc
      tripleCenterTriangle S i x = S.triangleOfPair (Sum.inl i) (Sum.inl j) (by simp [hij]) :=
        S.eq_triangleOfPair_of_contains (Sum.inl i) (Sum.inl j) (by simp [hij])
          (tripleCenterTriangle S i x)
          ⟨tripleCenterIndex S i x, tripleCenterIndex_spec S i x⟩
          ⟨tripleCenterIndex S j x, by rw [htriangle]; exact tripleCenterIndex_spec S j x⟩
      _ = T := (S.eq_triangleOfPair_of_contains (Sum.inl i) (Sum.inl j) (by simp [hij]) T
        ⟨i, hT i⟩ ⟨j, hT j⟩).symm
  have hleft_right : (Sum.inl (triplePointIndex S i x) : Fin 3 ⊕ β) = Sum.inr x := by
    calc
      Sum.inl (triplePointIndex S i x) = S.vertex T (triplePointIndex S i x) := (hT _).symm
      _ = S.vertex (tripleCenterTriangle S i x) (triplePointIndex S i x) := by rw [htoT]
      _ = Sum.inr x := triplePointIndex_spec S i x
  simp at hleft_right

private theorem tripleRemovedPacking_covers_iff
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j)
    (x y : β) (hxy : x ≠ y) :
    (tripleRemovedPacking S).CoversPair x y ↔
      ∀ i : Fin 3, (tripleLeavePairing S T hT i).perm x ≠ y := by
  constructor
  · rintro ⟨q, ⟨a, ha⟩, ⟨b, hb⟩⟩ i hpartner
    change tripleFreeVertex S q a = x at ha
    change tripleFreeVertex S q b = y at hb
    change triplePartner S T hT i x = y at hpartner
    have hqcenter : q.1 = tripleCenterTriangle S i x := by
      calc
        q.1 = S.triangleOfPair (Sum.inr x) (Sum.inr y) (by simpa using hxy) :=
          S.eq_triangleOfPair_of_contains (Sum.inr x) (Sum.inr y) (by simpa using hxy) q.1
            ⟨a, by simpa [ha] using tripleFreeVertex_source S q a⟩
            ⟨b, by simpa [hb] using tripleFreeVertex_source S q b⟩
        _ = tripleCenterTriangle S i x :=
          (S.eq_triangleOfPair_of_contains (Sum.inr x) (Sum.inr y) (by simpa using hxy)
            (tripleCenterTriangle S i x)
            ⟨triplePointIndex S i x, triplePointIndex_spec S i x⟩
            ⟨tripleThirdIndex S i x, by
              rw [triplePartner_spec S T hT i x, hpartner]⟩).symm
    rcases q.2 (tripleCenterIndex S i x) with ⟨z, hz⟩
    have hleft_right : (Sum.inl i : Fin 3 ⊕ β) = Sum.inr z := by
      calc
        Sum.inl i = S.vertex (tripleCenterTriangle S i x) (tripleCenterIndex S i x) :=
          (tripleCenterIndex_spec S i x).symm
        _ = S.vertex q.1 (tripleCenterIndex S i x) := by rw [hqcenter]
        _ = Sum.inr z := hz
    simp at hleft_right
  · intro h
    let t := S.triangleOfPair (Sum.inr x) (Sum.inr y) (by simpa using hxy)
    have hfree : ∀ k : Fin 3, ∃ z : β, S.vertex t k = Sum.inr z := by
      intro k
      cases hk : S.vertex t k with
      | inr z => exact ⟨z, rfl⟩
      | inl i =>
          have htc : t = tripleCenterTriangle S i x := by
            apply S.eq_triangleOfPair_of_contains (Sum.inl i) (Sum.inr x) (by simp) t
            · exact ⟨k, hk⟩
            · rcases S.pair_mem_triangleOfPair (Sum.inr x) (Sum.inr y) (by simpa using hxy) with
                ⟨⟨a, ha⟩, _⟩
              exact ⟨a, by simpa [t] using ha⟩
          have hycenter : ∃ l : Fin 3, S.vertex (tripleCenterTriangle S i x) l = Sum.inr y := by
            rcases S.pair_mem_triangleOfPair (Sum.inr x) (Sum.inr y) (by simpa using hxy) with
              ⟨_, ⟨b, hb⟩⟩
            exact ⟨b, by rw [← htc]; simpa [t] using hb⟩
          have hpartner : y = triplePartner S T hT i x :=
            triplePartner_eq_of_mem_centerTriangle S T hT i x y hxy hycenter
          exfalso
          apply h i
          change triplePartner S T hT i x = y
          exact hpartner.symm
    refine ⟨⟨t, hfree⟩, ?_, ?_⟩
    · rcases S.pair_mem_triangleOfPair (Sum.inr x) (Sum.inr y) (by simpa using hxy) with
        ⟨⟨a, ha⟩, _⟩
      refine ⟨a, ?_⟩
      apply Sum.inr.inj
      calc
        Sum.inr (tripleFreeVertex S ⟨t, hfree⟩ a) = S.vertex t a :=
          (tripleFreeVertex_source S ⟨t, hfree⟩ a).symm
        _ = Sum.inr x := by simpa [t] using ha
    · rcases S.pair_mem_triangleOfPair (Sum.inr x) (Sum.inr y) (by simpa using hxy) with
        ⟨_, ⟨b, hb⟩⟩
      refine ⟨b, ?_⟩
      apply Sum.inr.inj
      calc
        Sum.inr (tripleFreeVertex S ⟨t, hfree⟩ b) = S.vertex t b :=
          (tripleFreeVertex_source S ⟨t, hfree⟩ b).symm
        _ = Sum.inr y := by simpa [t] using hb

/-- Deleting the displayed triple from an STS produces three disjoint
matching leaves, all constructed from the source incidence data. -/
private noncomputable def tripleRemovedWithThreeMatchingLeaves
    (S : SteinerTripleSystem (Fin 3 ⊕ β)) (T : S.Triangle)
    (hT : ∀ j : Fin 3, S.vertex T j = Sum.inl j) :
    TrianglePacking.WithThreeMatchingLeaves β where
  packing := tripleRemovedPacking S
  matching := tripleLeavePairing S T hT
  matching_edges_disjoint := tripleLeavePairings_disjoint S T hT
  coversPair_iff := tripleRemovedPacking_covers_iff S T hT

end TripleRemovedSteiner

section TripleRemovedFinite

variable {n : ℕ}

/-- The three vertices of a displayed source triangle, viewed as a subtype of
the ambient finite carrier. -/
private noncomputable def tripleCentreEquiv
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :
    Fin 3 ≃ {x : Fin (n + 3) // ∃ i : Fin 3, S.vertex T i = x} := by
  refine Equiv.ofBijective (fun i => ⟨S.vertex T i, ⟨i, rfl⟩⟩) ?_
  constructor
  · intro i j hij
    apply S.vertex_injective T
    exact congrArg Subtype.val hij
  · rintro ⟨x, i, hi⟩
    exact ⟨i, Subtype.ext hi⟩

/-- The complement of a displayed triple. -/
private abbrev tripleFreePoints
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :=
  {x : Fin (n + 3) // ¬ ∃ i : Fin 3, S.vertex T i = x}

/-- Split the ambient carrier into the displayed triple and its complement. -/
private noncomputable def tripleCentrePartitionEquiv
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :
    Fin 3 ⊕ tripleFreePoints S T ≃ Fin (n + 3) := by
  classical
  let p : Fin (n + 3) → Prop := fun x => ∃ i : Fin 3, S.vertex T i = x
  exact (Equiv.sumCongr (tripleCentreEquiv S T) (Equiv.refl _)).trans
    (Equiv.sumCompl p)

private theorem tripleCentrePartitionEquiv_apply_left
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) (i : Fin 3) :
    tripleCentrePartitionEquiv S T (Sum.inl i) = S.vertex T i := by
  simp [tripleCentrePartitionEquiv, tripleCentreEquiv]

private theorem card_tripleFreePoints
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :
    Fintype.card (tripleFreePoints S T) = n := by
  classical
  let e := tripleCentrePartitionEquiv S T
  have hcard : Fintype.card (Fin 3 ⊕ tripleFreePoints S T) = n + 3 := by
    calc
      Fintype.card (Fin 3 ⊕ tripleFreePoints S T) =
          Fintype.card (Fin (n + 3)) := Fintype.card_congr e
      _ = n + 3 := Fintype.card_fin _
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  omega

private noncomputable def tripleRemovedWithThreeMatchingLeavesComplement
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :
    TrianglePacking.WithThreeMatchingLeaves (tripleFreePoints S T) := by
  classical
  let e := tripleCentrePartitionEquiv S T
  let S' : SteinerTripleSystem (Fin 3 ⊕ tripleFreePoints S T) :=
    SteinerTripleSystem.map e.symm S
  have hT : ∀ i : Fin 3, S'.vertex T i = Sum.inl i := by
    intro i
    change e.symm (S.vertex T i) = Sum.inl i
    apply e.injective
    rw [e.apply_symm_apply]
    exact (tripleCentrePartitionEquiv_apply_left S T i).symm
  exact tripleRemovedWithThreeMatchingLeaves S' T hT

/-- Deleting any displayed triple from an `STS(n+3)` gives a concrete
three-matching leave on `n` standard finite labels.  This is the macro input
for Feder--Subi's final `m ≡ 5 (mod 6)` case. -/
noncomputable def tripleRemovedWithThreeMatchingLeavesFin
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :
    TrianglePacking.WithThreeMatchingLeaves (Fin n) := by
  classical
  let e : tripleFreePoints S T ≃ Fin n :=
    Fintype.equivFinOfCardEq (card_tripleFreePoints S T)
  exact (tripleRemovedWithThreeMatchingLeavesComplement S T).map e

end TripleRemovedFinite

/-- Standard finite-label form of center removal: an `STS(m+1)` supplies a
packing of `K_m` with one perfect-matching leave. -/
noncomputable def centerRemovedWithMatchingLeaveFin
    (S : SteinerTripleSystem (Fin (m + 1))) : TrianglePacking.WithMatchingLeave (Fin m) := by
  let e : Option (Fin m) ≃ Fin (m + 1) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_option, Fintype.card_fin])
  exact centerRemovedWithMatchingLeave (SteinerTripleSystem.map e.symm S)

section KirkmanSixGroups

variable {α : Type} [Fintype α] [DecidableEq α]

private def fivePointResidualVertex : Bool → Fin 3 → ZMod 5
  | false, i => if i = 0 then 0 else if i = 1 then 1 else 2
  | true, i => if i = 0 then 0 else if i = 1 then 3 else 4

private def fivePointResidualPacking : TrianglePacking (ZMod 5) where
  Triangle := Bool
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := fivePointResidualVertex
  vertex_injective := by decide
  pair_covered_at_most_once := by decide

private def fivePointResidualLeaveVertex (i : Fin 4) : ZMod 5 :=
  if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 2 else 4

private theorem fivePointResidualPacking_leavesFourCycle :
    fivePointResidualPacking.LeavesFourCycle fivePointResidualLeaveVertex := by
  constructor
  · decide
  · intro x y hxy
    change (∃ t : Bool, (∃ i : Fin 3, fivePointResidualVertex t i = x) ∧
      ∃ j : Fin 3, fivePointResidualVertex t j = y) ↔
        ¬ ∃ i : Fin 4, s(x, y) =
          s(fivePointResidualLeaveVertex i, fivePointResidualLeaveVertex (fourCycleNext i))
    fin_cases x <;> fin_cases y
    all_goals first | exact False.elim (hxy rfl) | decide

private abbrev SixGroupFactorTriangleIndex (α : Type) :=
  Sigma fun _ : α => Sigma fun r : ZMod 5 => SixPointMatchingRepresentative r

private abbrev SixGroupTriangleIndex
    (S : SteinerTripleSystem α) :=
  Bool ⊕ (SixGroupFactorTriangleIndex α ⊕ (S.Triangle × (ZMod 6 × ZMod 6)))

/-- The factor triangle selected by a residual vertex, a six-point group, and
one endpoint in that group.  The representative quotient makes this an
unordered matching edge, rather than an oriented edge. -/
private noncomputable def sixGroupFactorTriangle
    (S : SteinerTripleSystem α) (a : α) (r : ZMod 5) (x : ZMod 6) :
    SixGroupTriangleIndex S :=
  Sum.inr (Sum.inl ⟨a, r, sixPointMatchingRepresentative r x⟩)

private noncomputable def sixGroupVertex
    (S : SteinerTripleSystem α) : SixGroupTriangleIndex S → Fin 3 →
      ZMod 5 ⊕ (α × ZMod 6)
  | Sum.inl p => fun i => Sum.inl (fivePointResidualPacking.vertex p i)
  | Sum.inr (Sum.inl ⟨a, r, x⟩) => fun i =>
      if i = 0 then Sum.inl r
      else if i = 1 then Sum.inr (a, x.1)
      else Sum.inr (a, (sixPointGroupFactorization.matching r).perm x.1)
  | Sum.inr (Sum.inr (t, p)) => fun i =>
      Sum.inr (S.vertex t i, (triplingCrossVertex p i).2)

private theorem sixGroupVertex_injective
    (S : SteinerTripleSystem α) (t : SixGroupTriangleIndex S) :
    Function.Injective (sixGroupVertex S t) := by
  cases t with
  | inl p =>
      intro i j hij
      apply fivePointResidualPacking.vertex_injective p
      exact Sum.inl.inj hij
  | inr t =>
      cases t with
      | inl q =>
          rcases q with ⟨a, r, x⟩
          intro i j hij
          fin_cases i
          · fin_cases j
            · rfl
            · simp [sixGroupVertex] at hij
            · simp [sixGroupVertex] at hij
          · fin_cases j
            · simp [sixGroupVertex] at hij
            · rfl
            · have hpartner : x.1 = (sixPointGroupFactorization.matching r).perm x.1 :=
                by simpa [sixGroupVertex] using hij
              exact False.elim ((sixPointGroupFactorization.matching r).apply_ne x.1 hpartner.symm)
          · fin_cases j
            · simp [sixGroupVertex] at hij
            · have hpartner : (sixPointGroupFactorization.matching r).perm x.1 = x.1 :=
                by simpa [sixGroupVertex] using hij
              exact False.elim ((sixPointGroupFactorization.matching r).apply_ne x.1 hpartner)
            · rfl
      | inr q =>
          rcases q with ⟨u, p⟩
          intro i j hij
          apply S.vertex_injective u
          exact congrArg (fun q : α × ZMod 6 => q.1) (Sum.inr.inj hij)

private theorem sixGroupFactorTriangle_residual_vertex
    (S : SteinerTripleSystem α) (a : α) (r : ZMod 5) (x : ZMod 6) :
    sixGroupVertex S (sixGroupFactorTriangle S a r x) 0 = Sum.inl r := by
  simp [sixGroupFactorTriangle, sixGroupVertex]

private theorem sixGroupFactorTriangle_group_vertex
    (S : SteinerTripleSystem α) (a : α) (r : ZMod 5) (x : ZMod 6) :
    ∃ i : Fin 3,
      sixGroupVertex S (sixGroupFactorTriangle S a r x) i = Sum.inr (a, x) := by
  rcases sixPointMatchingRepresentative_endpoints r x with hx | hx
  · refine ⟨1, ?_⟩
    change Sum.inr (a, (sixPointMatchingRepresentative r x).1) = Sum.inr (a, x)
    exact congrArg (fun z : ZMod 6 => Sum.inr (a, z)) hx.symm
  · refine ⟨2, ?_⟩
    change Sum.inr (a, (sixPointGroupFactorization.matching r).perm
      (sixPointMatchingRepresentative r x).1) = Sum.inr (a, x)
    exact congrArg (fun z : ZMod 6 => Sum.inr (a, z)) hx.symm

/-- A factor triangle that contains both a residual vertex `r` and a point
`(a,x)` is the canonical matching-edge triangle for those two vertices. -/
private theorem sixGroupFactorTriangleIndex_eq_of_residual_group
    (S : SteinerTripleSystem α) (a : α) (r : ZMod 5) (x : ZMod 6)
    (q : SixGroupFactorTriangleIndex α)
    (hr : ∃ i : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) i = Sum.inl r)
    (hx : ∃ j : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) j = Sum.inr (a, x)) :
    q = ⟨a, r, sixPointMatchingRepresentative r x⟩ := by
  rcases q with ⟨a', r', u⟩
  rcases hr with ⟨i, hi⟩
  fin_cases i
  · change Sum.inl r' = Sum.inl r at hi
    have hr' : r' = r := Sum.inl.inj hi
    subst r'
    rcases hx with ⟨j, hj⟩
    fin_cases j
    · simp [sixGroupVertex] at hj
    · change Sum.inr (a', u.1) = Sum.inr (a, x) at hj
      have hpair : (a', u.1) = (a, x) := Sum.inr.inj hj
      have ha : a' = a := congrArg Prod.fst hpair
      have hu : u.1 = x := congrArg Prod.snd hpair
      subst a'
      have hrep : sixPointMatchingRepresentative r x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint r u x (Or.inl hu.symm)
      rw [hrep]
    · change Sum.inr (a', (sixPointGroupFactorization.matching r).perm u.1) =
        Sum.inr (a, x) at hj
      have hpair : (a', (sixPointGroupFactorization.matching r).perm u.1) = (a, x) :=
        Sum.inr.inj hj
      have ha : a' = a := congrArg Prod.fst hpair
      have hu : (sixPointGroupFactorization.matching r).perm u.1 = x :=
        congrArg Prod.snd hpair
      subst a'
      have hrep : sixPointMatchingRepresentative r x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint r u x (Or.inr hu.symm)
      rw [hrep]
  · simp [sixGroupVertex] at hi
  · simp [sixGroupVertex] at hi

/-- A factor triangle containing two distinct points in one six-point group is
the unique matching-edge triangle determined by that unordered pair. -/
private theorem sixGroupFactorTriangleIndex_eq_of_group_pair
    (S : SteinerTripleSystem α) (a : α) (x y : ZMod 6) (hxy : x ≠ y)
    (q : SixGroupFactorTriangleIndex α)
    (hx : ∃ i : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) j = Sum.inr (a, y)) :
    q = ⟨a, sixPointGroupFactorization.factorOfPair x y hxy,
      sixPointMatchingRepresentative (sixPointGroupFactorization.factorOfPair x y hxy) x⟩ := by
  rcases q with ⟨a', r, u⟩
  rcases hx with ⟨i, hi⟩
  fin_cases i
  · simp [sixGroupVertex] at hi
  · change Sum.inr (a', u.1) = Sum.inr (a, x) at hi
    have hpair : (a', u.1) = (a, x) := Sum.inr.inj hi
    have ha : a' = a := congrArg Prod.fst hpair
    have hu : u.1 = x := congrArg Prod.snd hpair
    subst a'
    rcases hy with ⟨j, hj⟩
    fin_cases j
    · simp [sixGroupVertex] at hj
    · change Sum.inr (a, u.1) = Sum.inr (a, y) at hj
      exact False.elim (hxy (hu.symm.trans (congrArg Prod.snd (Sum.inr.inj hj))))
    · change Sum.inr (a, (sixPointGroupFactorization.matching r).perm u.1) =
        Sum.inr (a, y) at hj
      have hmatch_u : (sixPointGroupFactorization.matching r).perm u.1 = y :=
        congrArg Prod.snd (Sum.inr.inj hj)
      have hmatch : (sixPointGroupFactorization.matching r).perm x = y := by
        rw [← hu]
        exact hmatch_u
      have hr : r = sixPointGroupFactorization.factorOfPair x y hxy :=
        sixPointGroupFactorization.factorOfPair_eq_of_matching hxy r hmatch
      subst r
      have hrep : sixPointMatchingRepresentative
          (sixPointGroupFactorization.factorOfPair x y hxy) x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint _ u x (Or.inl hu.symm)
      rw [hrep]
  · change Sum.inr (a', (sixPointGroupFactorization.matching r).perm u.1) =
      Sum.inr (a, x) at hi
    have hpair : (a', (sixPointGroupFactorization.matching r).perm u.1) = (a, x) :=
      Sum.inr.inj hi
    have ha : a' = a := congrArg Prod.fst hpair
    have hmatch_u : (sixPointGroupFactorization.matching r).perm u.1 = x :=
      congrArg Prod.snd hpair
    subst a'
    rcases hy with ⟨j, hj⟩
    fin_cases j
    · simp [sixGroupVertex] at hj
    · change Sum.inr (a, u.1) = Sum.inr (a, y) at hj
      have hu : u.1 = y := congrArg Prod.snd (Sum.inr.inj hj)
      have hmatch : (sixPointGroupFactorization.matching r).perm x = y := by
        calc
          (sixPointGroupFactorization.matching r).perm x =
              (sixPointGroupFactorization.matching r).perm
                ((sixPointGroupFactorization.matching r).perm u.1) := by rw [hmatch_u]
          _ = u.1 := (sixPointGroupFactorization.matching r).apply_apply u.1
          _ = y := hu
      have hr : r = sixPointGroupFactorization.factorOfPair x y hxy :=
        sixPointGroupFactorization.factorOfPair_eq_of_matching hxy r hmatch
      subst r
      have hrep : sixPointMatchingRepresentative
          (sixPointGroupFactorization.factorOfPair x y hxy) x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint _ u x (Or.inr hmatch_u.symm)
      rw [hrep]
    · change Sum.inr (a, (sixPointGroupFactorization.matching r).perm u.1) =
        Sum.inr (a, y) at hj
      exact False.elim
        (hxy (hmatch_u.symm.trans (congrArg Prod.snd (Sum.inr.inj hj))))

/-- Two distinct residual vertices can occur together only in one of the two
literal triangles of the five-point residual packing. -/
private theorem sixGroupTriangle_eq_residual_of_covers_two_residual
    (S : SteinerTripleSystem α) (r s : ZMod 5) (hrs : r ≠ s)
    (t : SixGroupTriangleIndex S)
    (hr : ∃ i : Fin 3, sixGroupVertex S t i = Sum.inl r)
    (hs : ∃ j : Fin 3, sixGroupVertex S t j = Sum.inl s) :
    ∃ p : Bool, t = Sum.inl p ∧
      (∃ i : Fin 3, fivePointResidualPacking.vertex p i = r) ∧
      ∃ j : Fin 3, fivePointResidualPacking.vertex p j = s := by
  rcases hr with ⟨i, hi⟩
  rcases hs with ⟨j, hj⟩
  cases t with
  | inl p =>
      refine ⟨p, rfl, ?_, ?_⟩
      · exact ⟨i, Sum.inl.inj hi⟩
      · exact ⟨j, Sum.inl.inj hj⟩
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨a, r', u⟩
          have hri : r' = r := by
            fin_cases i
            · exact Sum.inl.inj hi
            · simp [sixGroupVertex] at hi
            · simp [sixGroupVertex] at hi
          have hsj : r' = s := by
            fin_cases j
            · exact Sum.inl.inj hj
            · simp [sixGroupVertex] at hj
            · simp [sixGroupVertex] at hj
          exact False.elim (hrs (hri.symm.trans hsj))
      | inr q =>
          fin_cases i <;> simp [sixGroupVertex] at hi

/-- A residual-to-group edge is present only in a six-point factor triangle. -/
private theorem sixGroupTriangle_eq_factor_of_covers_residual_group
    (S : SteinerTripleSystem α) (r : ZMod 5) (a : α) (x : ZMod 6)
    (t : SixGroupTriangleIndex S)
    (hr : ∃ i : Fin 3, sixGroupVertex S t i = Sum.inl r)
    (hx : ∃ j : Fin 3, sixGroupVertex S t j = Sum.inr (a, x)) :
    ∃ q : SixGroupFactorTriangleIndex α, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) i = Sum.inl r) ∧
      ∃ j : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) j = Sum.inr (a, x) := by
  rcases hr with ⟨i, hi⟩
  rcases hx with ⟨j, hj⟩
  cases t with
  | inl p =>
      fin_cases j <;> simp [sixGroupVertex] at hj
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          fin_cases i <;> simp [sixGroupVertex] at hi

/-- Two distinct points in the same six-point group can occur together only
in the matching triangle assigned to that group. -/
private theorem sixGroupTriangle_eq_factor_of_covers_same_group_pair
    (S : SteinerTripleSystem α) (a : α) (x y : ZMod 6) (hxy : x ≠ y)
    (t : SixGroupTriangleIndex S)
    (hx : ∃ i : Fin 3, sixGroupVertex S t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, sixGroupVertex S t j = Sum.inr (a, y)) :
    ∃ q : SixGroupFactorTriangleIndex α, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, sixGroupVertex S (Sum.inr (Sum.inl q)) j = Sum.inr (a, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p =>
      fin_cases i <;> simp [sixGroupVertex] at hi
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          rcases q with ⟨u, p⟩
          have hai : S.vertex u i = a :=
            congrArg Prod.fst (Sum.inr.inj hi)
          have haj : S.vertex u j = a :=
            congrArg Prod.fst (Sum.inr.inj hj)
          have hij : i = j := S.vertex_injective u (hai.trans haj.symm)
          apply False.elim
          apply hxy
          calc
            x = (triplingCrossVertex p i).2 :=
              (congrArg Prod.snd (Sum.inr.inj hi)).symm
            _ = (triplingCrossVertex p j).2 := by rw [hij]
            _ = y := congrArg Prod.snd (Sum.inr.inj hj)

/-- Points in two distinct six-point groups can occur together only in a
transversal triangle over a triangle of the input Steiner system. -/
private theorem sixGroupTriangle_eq_transversal_of_covers_distinct_groups
    (S : SteinerTripleSystem α) (a b : α) (x y : ZMod 6) (hab : a ≠ b)
    (t : SixGroupTriangleIndex S)
    (hx : ∃ i : Fin 3, sixGroupVertex S t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, sixGroupVertex S t j = Sum.inr (b, y)) :
    ∃ q : S.Triangle × (ZMod 6 × ZMod 6), t = Sum.inr (Sum.inr q) ∧
      (∃ i : Fin 3, sixGroupVertex S (Sum.inr (Sum.inr q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, sixGroupVertex S (Sum.inr (Sum.inr q)) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p =>
      fin_cases i <;> simp [sixGroupVertex] at hi
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨c, r, u⟩
          have hca : c = a := by
            fin_cases i
            · simp [sixGroupVertex] at hi
            · exact congrArg Prod.fst (Sum.inr.inj hi)
            · exact congrArg Prod.fst (Sum.inr.inj hi)
          have hcb : c = b := by
            fin_cases j
            · simp [sixGroupVertex] at hj
            · exact congrArg Prod.fst (Sum.inr.inj hj)
            · exact congrArg Prod.fst (Sum.inr.inj hj)
          exact False.elim (hab (hca.symm.trans hcb))
      | inr q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩

/-- The input Steiner triple and the cyclic transversal determine a unique
triangle for every pair of points in distinct six-point groups. -/
private theorem sixGroupTransversalTriangleIndex_eq_of_distinct_groups
    (S : SteinerTripleSystem α) (a b : α) (x y : ZMod 6) (hab : a ≠ b)
    (q q' : S.Triangle × (ZMod 6 × ZMod 6))
    (hx : ∃ i : Fin 3, sixGroupVertex S (Sum.inr (Sum.inr q)) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, sixGroupVertex S (Sum.inr (Sum.inr q)) j = Sum.inr (b, y))
    (hx' : ∃ i : Fin 3, sixGroupVertex S (Sum.inr (Sum.inr q')) i = Sum.inr (a, x))
    (hy' : ∃ j : Fin 3, sixGroupVertex S (Sum.inr (Sum.inr q')) j = Sum.inr (b, y)) :
    q = q' := by
  rcases q with ⟨t, p⟩
  rcases q' with ⟨u, p'⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  rcases hx' with ⟨k, hk⟩
  rcases hy' with ⟨l, hl⟩
  have hai : S.vertex t i = a := congrArg Prod.fst (Sum.inr.inj hi)
  have hbj : S.vertex t j = b := congrArg Prod.fst (Sum.inr.inj hj)
  have hak : S.vertex u k = a := congrArg Prod.fst (Sum.inr.inj hk)
  have hbl : S.vertex u l = b := congrArg Prod.fst (Sum.inr.inj hl)
  have hix : (triplingCrossVertex p i).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [sixGroupVertex] using hi))
  have hjy : (triplingCrossVertex p j).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [sixGroupVertex] using hj))
  have hkx : (triplingCrossVertex p' k).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [sixGroupVertex] using hk))
  have hly : (triplingCrossVertex p' l).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [sixGroupVertex] using hl))
  have ht : t = S.triangleOfPair a b hab :=
    S.eq_triangleOfPair_of_contains a b hab t ⟨i, hai⟩ ⟨j, hbj⟩
  have hu : u = S.triangleOfPair a b hab :=
    S.eq_triangleOfPair_of_contains a b hab u ⟨k, hak⟩ ⟨l, hbl⟩
  subst t
  subst u
  have hik : i = k := S.vertex_injective (S.triangleOfPair a b hab) (hai.trans hak.symm)
  have hjl : j = l := S.vertex_injective (S.triangleOfPair a b hab) (hbj.trans hbl.symm)
  subst k
  subst l
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = S.vertex (S.triangleOfPair a b hab) i := hai.symm
      _ = S.vertex (S.triangleOfPair a b hab) j := by rw [hij]
      _ = b := hbj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p₀, hp₀, hp₀uniq⟩
  have hp :
      (∃ h : Fin 3, triplingCrossVertex p h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hix
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hjy
  have hp' :
      (∃ h : Fin 3, triplingCrossVertex p' h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p' h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hkx
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hly
  have hpp : p = p' := (hp₀uniq p hp).trans (hp₀uniq p' hp').symm
  subst p'
  rfl

private theorem sixGroupPacking_pair_covered_at_most_once
    (S : SteinerTripleSystem α) :
    ∀ x y : ZMod 5 ⊕ (α × ZMod 6), x ≠ y → ∀ t u : SixGroupTriangleIndex S,
      (∃ i : Fin 3, sixGroupVertex S t i = x) →
      (∃ j : Fin 3, sixGroupVertex S t j = y) →
      (∃ i : Fin 3, sixGroupVertex S u i = x) →
      (∃ j : Fin 3, sixGroupVertex S u j = y) → t = u := by
  rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hxy t u htx hty hux huy
  · have hrs : r ≠ s := by
      intro hrs
      apply hxy
      rw [hrs]
    rcases sixGroupTriangle_eq_residual_of_covers_two_residual S r s hrs t htx hty with
      ⟨p, hp, hpr, hps⟩
    rcases sixGroupTriangle_eq_residual_of_covers_two_residual S r s hrs u hux huy with
      ⟨q, hq, hqr, hqs⟩
    calc
      t = Sum.inl p := hp
      _ = Sum.inl q := congrArg Sum.inl
        (fivePointResidualPacking.pair_covered_at_most_once r s hrs p q hpr hps hqr hqs)
      _ = u := hq.symm
  · rcases sixGroupTriangle_eq_factor_of_covers_residual_group S r b y t htx hty with
      ⟨q, hq, hqr, hqy⟩
    rcases sixGroupTriangle_eq_factor_of_covers_residual_group S r b y u hux huy with
      ⟨q', hq', hq'r, hq'y⟩
    have hcanon : q = ⟨b, r, sixPointMatchingRepresentative r y⟩ :=
      sixGroupFactorTriangleIndex_eq_of_residual_group S b r y q hqr hqy
    have hcanon' : q' = ⟨b, r, sixPointMatchingRepresentative r y⟩ :=
      sixGroupFactorTriangleIndex_eq_of_residual_group S b r y q' hq'r hq'y
    calc
      t = Sum.inr (Sum.inl q) := hq
      _ = Sum.inr (Sum.inl q') := by rw [hcanon, hcanon']
      _ = u := hq'.symm
  · rcases sixGroupTriangle_eq_factor_of_covers_residual_group S s a x t hty htx with
      ⟨q, hq, hqs, hqx⟩
    rcases sixGroupTriangle_eq_factor_of_covers_residual_group S s a x u huy hux with
      ⟨q', hq', hq's, hq'x⟩
    have hcanon : q = ⟨a, s, sixPointMatchingRepresentative s x⟩ :=
      sixGroupFactorTriangleIndex_eq_of_residual_group S a s x q hqs hqx
    have hcanon' : q' = ⟨a, s, sixPointMatchingRepresentative s x⟩ :=
      sixGroupFactorTriangleIndex_eq_of_residual_group S a s x q' hq's hq'x
    calc
      t = Sum.inr (Sum.inl q) := hq
      _ = Sum.inr (Sum.inl q') := by rw [hcanon, hcanon']
      _ = u := hq'.symm
  · by_cases hab : a = b
    · subst b
      have hxy' : x ≠ y := by
        intro hxy'
        apply hxy
        simp [hxy']
      rcases sixGroupTriangle_eq_factor_of_covers_same_group_pair S a x y hxy' t htx hty with
        ⟨q, hq, hqx, hqy⟩
      rcases sixGroupTriangle_eq_factor_of_covers_same_group_pair S a x y hxy' u hux huy with
        ⟨q', hq', hq'x, hq'y⟩
      have hcanon : q = ⟨a, sixPointGroupFactorization.factorOfPair x y hxy',
          sixPointMatchingRepresentative (sixPointGroupFactorization.factorOfPair x y hxy') x⟩ :=
        sixGroupFactorTriangleIndex_eq_of_group_pair S a x y hxy' q hqx hqy
      have hcanon' : q' = ⟨a, sixPointGroupFactorization.factorOfPair x y hxy',
          sixPointMatchingRepresentative (sixPointGroupFactorization.factorOfPair x y hxy') x⟩ :=
        sixGroupFactorTriangleIndex_eq_of_group_pair S a x y hxy' q' hq'x hq'y
      calc
        t = Sum.inr (Sum.inl q) := hq
        _ = Sum.inr (Sum.inl q') := by rw [hcanon, hcanon']
        _ = u := hq'.symm
    · rcases sixGroupTriangle_eq_transversal_of_covers_distinct_groups S a b x y hab t htx hty with
        ⟨q, hq, hqx, hqy⟩
      rcases sixGroupTriangle_eq_transversal_of_covers_distinct_groups S a b x y hab u hux huy with
        ⟨q', hq', hq'x, hq'y⟩
      have hqq' : q = q' :=
        sixGroupTransversalTriangleIndex_eq_of_distinct_groups S a b x y hab q q'
          hqx hqy hq'x hq'y
      calc
        t = Sum.inr (Sum.inr q) := hq
        _ = Sum.inr (Sum.inr q') := congrArg (fun z => Sum.inr (Sum.inr z)) hqq'
        _ = u := hq'.symm

/-- Feder--Subi's six-point-group step: from an STS on `α`, form a triangle
packing on five residual points together with one six-point group above every
point of `α`.  Its only intended uncovered edges are among the residual five
points. -/
noncomputable def sixGroupPacking (S : SteinerTripleSystem α) :
    TrianglePacking (ZMod 5 ⊕ (α × ZMod 6)) where
  Triangle := SixGroupTriangleIndex S
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := sixGroupVertex S
  vertex_injective := sixGroupVertex_injective S
  pair_covered_at_most_once := sixGroupPacking_pair_covered_at_most_once S

private theorem sixGroupPacking_covers_residual_group
    (S : SteinerTripleSystem α) (r : ZMod 5) (a : α) (x : ZMod 6) :
    (sixGroupPacking S).CoversPair (Sum.inl r) (Sum.inr (a, x)) := by
  refine ⟨sixGroupFactorTriangle S a r x, ⟨0,
    sixGroupFactorTriangle_residual_vertex S a r x⟩,
    sixGroupFactorTriangle_group_vertex S a r x⟩

private theorem sixGroupFactorTriangle_covers_matching_edge
    (S : SteinerTripleSystem α) (a : α) (r : ZMod 5) (x y : ZMod 6)
    (hxy : (sixPointGroupFactorization.matching r).perm x = y) :
    ∃ i : Fin 3,
      sixGroupVertex S (sixGroupFactorTriangle S a r x) i = Sum.inr (a, y) := by
  have hrep : sixPointMatchingRepresentative r y = sixPointMatchingRepresentative r x := by
    rcases sixPointMatchingRepresentative_endpoints r x with hx | hx
    · apply sixPointMatchingRepresentative_eq_of_endpoint r
        (sixPointMatchingRepresentative r x) y
      right
      calc
        y = (sixPointGroupFactorization.matching r).perm x := hxy.symm
        _ = (sixPointGroupFactorization.matching r).perm
              (sixPointMatchingRepresentative r x).1 :=
          congrArg (sixPointGroupFactorization.matching r).perm hx
    · apply sixPointMatchingRepresentative_eq_of_endpoint r
        (sixPointMatchingRepresentative r x) y
      left
      calc
        y = (sixPointGroupFactorization.matching r).perm x := hxy.symm
        _ = (sixPointGroupFactorization.matching r).perm
              ((sixPointGroupFactorization.matching r).perm
                (sixPointMatchingRepresentative r x).1) :=
          congrArg (sixPointGroupFactorization.matching r).perm hx
        _ = (sixPointMatchingRepresentative r x).1 :=
          (sixPointGroupFactorization.matching r).apply_apply _
  rcases sixGroupFactorTriangle_group_vertex S a r y with ⟨i, hi⟩
  have htriangle : sixGroupFactorTriangle S a r y = sixGroupFactorTriangle S a r x := by
    unfold sixGroupFactorTriangle
    rw [hrep]
  rw [htriangle] at hi
  exact ⟨i, hi⟩

private theorem sixGroupPacking_covers_same_group_pair
    (S : SteinerTripleSystem α) (a : α) (x y : ZMod 6) (hxy : x ≠ y) :
    (sixGroupPacking S).CoversPair (Sum.inr (a, x)) (Sum.inr (a, y)) := by
  let r := sixPointGroupFactorization.factorOfPair x y hxy
  have hmatch : (sixPointGroupFactorization.matching r).perm x = y :=
    sixPointGroupFactorization.matching_factorOfPair x y hxy
  refine ⟨sixGroupFactorTriangle S a r x,
    sixGroupFactorTriangle_group_vertex S a r x,
    sixGroupFactorTriangle_covers_matching_edge S a r x y hmatch⟩

private theorem sixGroupPacking_covers_distinct_groups
    (S : SteinerTripleSystem α) (a b : α) (x y : ZMod 6) (hab : a ≠ b) :
    (sixGroupPacking S).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  let t := S.triangleOfPair a b hab
  rcases S.pair_mem_triangleOfPair a b hab with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = S.vertex t i := by simpa [t] using hi.symm
      _ = S.vertex t j := by rw [hij]
      _ = b := by simpa [t] using hj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p, hp, hpuniq⟩
  rcases hp with ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hki : k = i := triplingCrossVertex_index_eq_fst hk
  have hlj : l = j := triplingCrossVertex_index_eq_fst hl
  subst k
  subst l
  refine ⟨Sum.inr (Sum.inr (t, p)), ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · change Sum.inr (S.vertex t i, (triplingCrossVertex p i).2) = Sum.inr (a, x)
    apply congrArg Sum.inr
    have hmacro : S.vertex t i = a := by simpa [t] using hi
    have hoffset : (triplingCrossVertex p i).2 = x := congrArg Prod.snd hk
    rw [hmacro, hoffset]
  · change Sum.inr (S.vertex t j, (triplingCrossVertex p j).2) = Sum.inr (b, y)
    apply congrArg Sum.inr
    have hmacro : S.vertex t j = b := by simpa [t] using hj
    have hoffset : (triplingCrossVertex p j).2 = y := congrArg Prod.snd hl
    rw [hmacro, hoffset]

/-- The four leave vertices remain in the five-point residual component. -/
private def sixGroupLeaveVertex (i : Fin 4) : ZMod 5 ⊕ (α × ZMod 6) :=
  Sum.inl (fivePointResidualLeaveVertex i)

private theorem sixGroupPacking_covers_residual_pair_iff
    (S : SteinerTripleSystem α) (r s : ZMod 5) (hrs : r ≠ s) :
    (sixGroupPacking S).CoversPair (Sum.inl r) (Sum.inl s) ↔
      fivePointResidualPacking.CoversPair r s := by
  constructor
  · rintro ⟨t, hr, hs⟩
    rcases sixGroupTriangle_eq_residual_of_covers_two_residual S r s hrs t hr hs with
      ⟨p, hp, hpr, hps⟩
    exact ⟨p, hpr, hps⟩
  · rintro ⟨p, hpr, hps⟩
    rcases hpr with ⟨i, hi⟩
    rcases hps with ⟨j, hj⟩
    refine ⟨Sum.inl p, ⟨i, ?_⟩, ⟨j, ?_⟩⟩
    · exact congrArg Sum.inl hi
    · exact congrArg Sum.inl hj

private theorem sixGroupLeave_cycle_iff (r s : ZMod 5) :
    (∃ i : Fin 4, s(Sum.inl r, Sum.inl s) =
      s(sixGroupLeaveVertex (α := α) i,
        sixGroupLeaveVertex (α := α) (fourCycleNext i))) ↔
      ∃ i : Fin 4, s(r, s) =
        s(fivePointResidualLeaveVertex i, fivePointResidualLeaveVertex (fourCycleNext i)) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Sym2.map.injective (fun x y h => Sum.inl.inj h)
    simpa only [Sym2.map_mk, sixGroupLeaveVertex] using hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa only [Sym2.map_mk, sixGroupLeaveVertex] using congrArg (Sym2.map Sum.inl) hi

/-- The Feder--Subi six-point-group construction leaves precisely the displayed
four-cycle inherited from its five residual points. -/
theorem sixGroupPacking_leavesFourCycle (S : SteinerTripleSystem α) :
    (sixGroupPacking S).LeavesFourCycle (sixGroupLeaveVertex (α := α)) := by
  constructor
  · intro i j hij
    apply fivePointResidualPacking_leavesFourCycle.1
    exact Sum.inl.inj hij
  · rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hxy
    · have hrs : r ≠ s := by
        intro hrs
        apply hxy
        rw [hrs]
      constructor
      · intro hcover
        have hbase : fivePointResidualPacking.CoversPair r s :=
          (sixGroupPacking_covers_residual_pair_iff S r s hrs).mp hcover
        have hnotbase : ¬ ∃ i : Fin 4, s(r, s) =
            s(fivePointResidualLeaveVertex i, fivePointResidualLeaveVertex (fourCycleNext i)) :=
          (fivePointResidualPacking_leavesFourCycle.2 r s hrs).mp hbase
        intro hcycle
        apply hnotbase
        exact (sixGroupLeave_cycle_iff (α := α) r s).mp hcycle
      · intro hnotcycle
        apply (sixGroupPacking_covers_residual_pair_iff S r s hrs).mpr
        apply (fivePointResidualPacking_leavesFourCycle.2 r s hrs).mpr
        intro hbasecycle
        apply hnotcycle
        exact (sixGroupLeave_cycle_iff (α := α) r s).mpr hbasecycle
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨_, hright⟩ | ⟨_, hright⟩
        · simp [sixGroupLeaveVertex] at hright
        · simp [sixGroupLeaveVertex] at hright
      · intro hnotcycle
        exact sixGroupPacking_covers_residual_group S r b y
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [sixGroupLeaveVertex] at hleft
        · simp [sixGroupLeaveVertex] at hleft
      · intro hnotcycle
        rcases sixGroupPacking_covers_residual_group S s a x with ⟨t, hs, ha⟩
        exact ⟨t, ha, hs⟩
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [sixGroupLeaveVertex] at hleft
        · simp [sixGroupLeaveVertex] at hleft
      · intro hnotcycle
        by_cases hab : a = b
        · subst b
          have hxy' : x ≠ y := by
            intro hxy'
            apply hxy
            simp [hxy']
          exact sixGroupPacking_covers_same_group_pair S a x y hxy'
        · exact sixGroupPacking_covers_distinct_groups S a b x y hab

/-- The six-point-group construction has a concrete four-cycle leave.  This
existential interface is stable under later relabelings of the carrier. -/
theorem exists_sixGroupPacking_leavesFourCycle (S : SteinerTripleSystem α) :
    ∃ v : Fin 4 → ZMod 5 ⊕ (α × ZMod 6),
      (sixGroupPacking S).LeavesFourCycle v :=
  ⟨sixGroupLeaveVertex, sixGroupPacking_leavesFourCycle S⟩

private theorem card_sixGroupCarrier (m : ℕ) :
    Fintype.card (ZMod 5 ⊕ (Fin m × ZMod 6)) = 6 * m + 5 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  omega

/-- The six-point-group packing relabeled to the standard finite carrier of
size `6m+5`. -/
noncomputable def sixGroupPackingFin (S : SteinerTripleSystem (Fin m)) :
    TrianglePacking (Fin (6 * m + 5)) := by
  let e : ZMod 5 ⊕ (Fin m × ZMod 6) ≃ Fin (6 * m + 5) :=
    Fintype.equivFinOfCardEq (card_sixGroupCarrier m)
  exact (sixGroupPacking S).map e

/-- Feder--Subi's group-six step yields a near-decomposition of `K_{6m+5}`
whenever its `m` group labels carry a Steiner triple system. -/
theorem exists_sixGroupPackingFin_leavesFourCycle (S : SteinerTripleSystem (Fin m)) :
    ∃ v : Fin 4 → Fin (6 * m + 5),
      (sixGroupPackingFin S).LeavesFourCycle v := by
  let e : ZMod 5 ⊕ (Fin m × ZMod 6) ≃ Fin (6 * m + 5) :=
    Fintype.equivFinOfCardEq (card_sixGroupCarrier m)
  refine ⟨e ∘ sixGroupLeaveVertex, ?_⟩
  exact TrianglePacking.map_leavesFourCycle e (sixGroupPacking S) sixGroupLeaveVertex
    (sixGroupPacking_leavesFourCycle S)

section DenseSplitBlocks

open AppliedModelingLib.Foundations.Graph

/-- A fixed finite ordering lets a fixed-point-free involution select exactly
one representative for each of its unordered matching edges. -/
private noncomputable def finiteOrderEquiv : α ≃ Fin (Fintype.card α) :=
  Fintype.equivFinOfCardEq rfl

private abbrev MatchingRepresentative (M : EvenPairing α) :=
  {a : α // (finiteOrderEquiv a).val < (finiteOrderEquiv (M.perm a)).val}

private noncomputable def matchingRepresentative (M : EvenPairing α) (a : α) :
    MatchingRepresentative M :=
  if ha : (finiteOrderEquiv a).val < (finiteOrderEquiv (M.perm a)).val then
    ⟨a, ha⟩
  else
    ⟨M.perm a, by
      have hne : M.perm a ≠ a := M.apply_ne a
      have hvalne : (finiteOrderEquiv (M.perm a)).val ≠ (finiteOrderEquiv a).val := by
        intro h
        apply hne
        apply finiteOrderEquiv.injective
        exact Fin.ext h
      rw [M.apply_apply]
      omega⟩

private theorem matchingRepresentative_eq_self
    (M : EvenPairing α) (u : MatchingRepresentative M) :
    matchingRepresentative M u.1 = u := by
  apply Subtype.ext
  simp [matchingRepresentative, u.2]

private theorem matchingRepresentative_perm_eq_self
    (M : EvenPairing α) (u : MatchingRepresentative M) :
    matchingRepresentative M (M.perm u.1) = u := by
  apply Subtype.ext
  have hnot : ¬ (finiteOrderEquiv (M.perm u.1)).val <
      (finiteOrderEquiv (M.perm (M.perm u.1))).val := by
    rw [M.apply_apply]
    omega
  rw [M.apply_apply] at hnot
  simp [matchingRepresentative, hnot, M.apply_apply]

private theorem matchingRepresentative_endpoints
    (M : EvenPairing α) (a : α) :
    a = (matchingRepresentative M a).1 ∨
      a = M.perm (matchingRepresentative M a).1 := by
  unfold matchingRepresentative
  split
  · exact Or.inl rfl
  · exact Or.inr (M.apply_apply a).symm

private theorem matchingRepresentative_eq_of_endpoint
    (M : EvenPairing α) (u : MatchingRepresentative M) (a : α)
    (ha : a = u.1 ∨ a = M.perm u.1) : matchingRepresentative M a = u := by
  rcases ha with ha | ha
  · subst a
    exact matchingRepresentative_eq_self M u
  · subst a
    exact matchingRepresentative_perm_eq_self M u

private noncomputable def finFiveEquivZModFive : Fin 5 ≃ ZMod 5 :=
  (Fintype.equivFinOfCardEq (by norm_num [ZMod.card])).symm

private noncomputable def finTwelveEquivFinTwoZModSix : Fin 12 ≃ Fin 2 × ZMod 6 := by
  let e1 : Fin 12 ≃ Fin 12 := Fintype.equivFinOfCardEq rfl
  let e2 : Fin 2 × ZMod 6 ≃ Fin 12 :=
    Fintype.equivFinOfCardEq (by norm_num [Fintype.card_prod, ZMod.card])
  exact e1.trans e2.symm

/-- Embed one literal dense-split block on a matching pair of macro labels.
The 12 clique points are the two six-point fibres of that matching edge. -/
private noncomputable def denseSplitBlockMap (M : EvenPairing α)
    (u : MatchingRepresentative M) : Fin 5 ⊕ Fin 12 → ZMod 5 ⊕ (α × ZMod 6)
  | Sum.inl r => Sum.inl (finFiveEquivZModFive r)
  | Sum.inr s =>
      let q := finTwelveEquivFinTwoZModSix s
      if q.1 = 0 then Sum.inr (u.1, q.2)
      else Sum.inr (M.perm u.1, q.2)

private noncomputable def denseSplitBlockVertex (M : EvenPairing α)
    (u : MatchingRepresentative M) (t : denseSplitFiveTwelve.Triangle) (i : Fin 3) :
    ZMod 5 ⊕ (α × ZMod 6) :=
  denseSplitBlockMap M u (denseSplitFiveTwelve.vertex t i)

private noncomputable def denseSplitBlockRetract (M : EvenPairing α)
    (u : MatchingRepresentative M) : ZMod 5 ⊕ (α × ZMod 6) → Fin 5 ⊕ Fin 12
  | Sum.inl r => Sum.inl (finFiveEquivZModFive.symm r)
  | Sum.inr (a, x) =>
      if a = u.1 then Sum.inr (finTwelveEquivFinTwoZModSix.symm (0, x))
      else Sum.inr (finTwelveEquivFinTwoZModSix.symm (1, x))

private theorem denseSplitBlockRetract_apply (M : EvenPairing α)
    (u : MatchingRepresentative M) :
    Function.LeftInverse (denseSplitBlockRetract M u) (denseSplitBlockMap M u) := by
  intro z
  cases z with
  | inl r =>
      simp [denseSplitBlockMap, denseSplitBlockRetract]
  | inr s =>
      cases hs : finTwelveEquivFinTwoZModSix s with
      | mk g x =>
          fin_cases g
          · simp [denseSplitBlockMap, denseSplitBlockRetract, hs]
            apply finTwelveEquivFinTwoZModSix.injective
            simpa using hs.symm
          · have hne : M.perm u.1 ≠ u.1 := M.apply_ne u.1
            simp [denseSplitBlockMap, denseSplitBlockRetract, hs, hne]
            apply finTwelveEquivFinTwoZModSix.injective
            simpa using hs.symm

private theorem denseSplitBlockMap_injective (M : EvenPairing α)
    (u : MatchingRepresentative M) : Function.Injective (denseSplitBlockMap M u) :=
  (denseSplitBlockRetract_apply M u).injective

private theorem denseSplitBlockVertex_injective (M : EvenPairing α)
    (u : MatchingRepresentative M) (t : denseSplitFiveTwelve.Triangle) :
    Function.Injective (denseSplitBlockVertex M u t) :=
  (denseSplitBlockMap_injective M u).comp (denseSplitFiveTwelve.vertex_injective t)

/-- One finite dense-split block placed on a selected matching edge of the
macro carrier.  Its triangle type remains the checked literal base type. -/
private noncomputable def denseSplitBlockPacking (M : EvenPairing α)
    (u : MatchingRepresentative M) : TrianglePacking (ZMod 5 ⊕ (α × ZMod 6)) where
  Triangle := denseSplitFiveTwelve.Triangle
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := denseSplitBlockVertex M u
  vertex_injective := denseSplitBlockVertex_injective M u
  pair_covered_at_most_once := by
    intro x y hxy t q htx hty hqx hqy
    rcases htx with ⟨i, hi⟩
    rcases hty with ⟨j, hj⟩
    rcases hqx with ⟨k, hk⟩
    rcases hqy with ⟨l, hl⟩
    have hik : denseSplitFiveTwelve.vertex t i = denseSplitFiveTwelve.vertex q k :=
      denseSplitBlockMap_injective M u (by
        calc
          denseSplitBlockMap M u (denseSplitFiveTwelve.vertex t i) = x := hi
          _ = denseSplitBlockMap M u (denseSplitFiveTwelve.vertex q k) := hk.symm)
    have hjl : denseSplitFiveTwelve.vertex t j = denseSplitFiveTwelve.vertex q l :=
      denseSplitBlockMap_injective M u (by
        calc
          denseSplitBlockMap M u (denseSplitFiveTwelve.vertex t j) = y := hj
          _ = denseSplitBlockMap M u (denseSplitFiveTwelve.vertex q l) := hl.symm)
    have hij : denseSplitFiveTwelve.vertex t i ≠ denseSplitFiveTwelve.vertex t j := by
      intro h
      apply hxy
      calc
        x = denseSplitBlockMap M u (denseSplitFiveTwelve.vertex t i) := hi.symm
        _ = denseSplitBlockMap M u (denseSplitFiveTwelve.vertex t j) := by rw [h]
        _ = y := hj
    exact denseSplitFiveTwelve.pair_covered_at_most_once
      (denseSplitFiveTwelve.vertex t i) (denseSplitFiveTwelve.vertex t j) hij t q
      ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, hik.symm⟩ ⟨l, hjl.symm⟩

private theorem denseSplitBlockPacking_covers_of_base
    (M : EvenPairing α) (u : MatchingRepresentative M) {z w : Fin 5 ⊕ Fin 12}
    (hzw : denseSplitFiveTwelve.CoversPair z w) :
    (denseSplitBlockPacking M u).CoversPair
      (denseSplitBlockMap M u z) (denseSplitBlockMap M u w) := by
  rcases hzw with ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  exact ⟨t, ⟨i, congrArg (denseSplitBlockMap M u) hi⟩,
    ⟨j, congrArg (denseSplitBlockMap M u) hj⟩⟩

private abbrev MatchingBlockTriangleIndex (M : EvenPairing α) :=
  Sigma fun u : MatchingRepresentative M => denseSplitFiveTwelve.Triangle

private abbrev MatchingLeaveTriangleIndex
    (L : TrianglePacking.WithMatchingLeave α) :=
  Bool ⊕ (MatchingBlockTriangleIndex L.matching ⊕
    (L.packing.Triangle × (ZMod 6 × ZMod 6)))

private noncomputable def matchingLeaveVertex
    (L : TrianglePacking.WithMatchingLeave α) : MatchingLeaveTriangleIndex L → Fin 3 →
      ZMod 5 ⊕ (α × ZMod 6)
  | Sum.inl p => fun i => Sum.inl (fivePointResidualPacking.vertex p i)
  | Sum.inr (Sum.inl ⟨u, t⟩) => denseSplitBlockVertex L.matching u t
  | Sum.inr (Sum.inr (t, p)) => fun i =>
      Sum.inr (L.packing.vertex t i, (triplingCrossVertex p i).2)

private theorem matchingLeaveVertex_injective
    (L : TrianglePacking.WithMatchingLeave α) (t : MatchingLeaveTriangleIndex L) :
    Function.Injective (matchingLeaveVertex L t) := by
  cases t with
  | inl p =>
      intro i j hij
      apply fivePointResidualPacking.vertex_injective p
      exact Sum.inl.inj hij
  | inr t =>
      cases t with
      | inl q =>
          rcases q with ⟨u, t⟩
          exact denseSplitBlockVertex_injective L.matching u t
      | inr q =>
          rcases q with ⟨t, p⟩
          intro i j hij
          apply L.packing.vertex_injective t
          exact congrArg (fun q : α × ZMod 6 => q.1) (Sum.inr.inj hij)

private theorem denseSplitBlockMap_right_macro
    (M : EvenPairing α) (u : MatchingRepresentative M) (z : Fin 5 ⊕ Fin 12)
    (a : α) (x : ZMod 6)
    (h : denseSplitBlockMap M u z = Sum.inr (a, x)) :
    a = u.1 ∨ a = M.perm u.1 := by
  cases z with
  | inl r => simp [denseSplitBlockMap] at h
  | inr s =>
      let q := finTwelveEquivFinTwoZModSix s
      by_cases hq : q.1 = 0
      · left
        have hpair : (u.1, q.2) = (a, x) := by
          simpa [denseSplitBlockMap, q, hq] using h
        exact (congrArg Prod.fst hpair).symm
      · right
        have hpair : (M.perm u.1, q.2) = (a, x) := by
          simpa [denseSplitBlockMap, q, hq] using h
        exact (congrArg Prod.fst hpair).symm

private theorem matchingRepresentative_eq_of_block_contains
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (t : denseSplitFiveTwelve.Triangle) (a : α) (x : ZMod 6)
    (h : ∃ i : Fin 3, denseSplitBlockVertex M u t i = Sum.inr (a, x)) :
    u = matchingRepresentative M a := by
  rcases h with ⟨i, hi⟩
  apply (matchingRepresentative_eq_of_endpoint M u a
    (denseSplitBlockMap_right_macro M u (denseSplitFiveTwelve.vertex t i) a x hi)).symm

/-- A dense-split block containing a group point has a uniquely determined
matching edge.  Within that fixed literal block, pair uniqueness is inherited
from the checked 17-point base packing. -/
private theorem matchingBlockTriangleIndex_eq_of_contains_right_pair
    (M : EvenPairing α) (a : α) (x : ZMod 6)
    (y : ZMod 5 ⊕ (α × ZMod 6))
    (hxy : Sum.inr (a, x) ≠ y)
    (u v : MatchingRepresentative M)
    (t q : denseSplitFiveTwelve.Triangle)
    (htx : ∃ i : Fin 3, denseSplitBlockVertex M u t i = Sum.inr (a, x))
    (hty : ∃ j : Fin 3, denseSplitBlockVertex M u t j = y)
    (hqx : ∃ i : Fin 3, denseSplitBlockVertex M v q i = Sum.inr (a, x))
    (hqy : ∃ j : Fin 3, denseSplitBlockVertex M v q j = y) :
    (⟨u, t⟩ : MatchingBlockTriangleIndex M) = ⟨v, q⟩ := by
  have hu : u = matchingRepresentative M a :=
    matchingRepresentative_eq_of_block_contains M u t a x htx
  have hv : v = matchingRepresentative M a :=
    matchingRepresentative_eq_of_block_contains M v q a x hqx
  subst u
  subst v
  congr 1
  exact (denseSplitBlockPacking M (matchingRepresentative M a)).pair_covered_at_most_once
    (Sum.inr (a, x)) y hxy t q htx hty hqx hqy

private theorem denseSplitBlockPacking_not_covers_residual_pair
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (r s : ZMod 5) (hrs : r ≠ s) :
    ¬ (denseSplitBlockPacking M u).CoversPair (Sum.inl r) (Sum.inl s) := by
  rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  apply denseSplitFiveTwelve_not_covers_residual_pair
    (finFiveEquivZModFive.symm r) (finFiveEquivZModFive.symm s)
    (fun h => hrs (finFiveEquivZModFive.symm.injective h))
  refine ⟨t, ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · apply denseSplitBlockMap_injective M u
    calc
      denseSplitBlockMap M u (denseSplitFiveTwelve.vertex t i) = Sum.inl r := hi
      _ = denseSplitBlockMap M u (Sum.inl (finFiveEquivZModFive.symm r)) := by
        simp [denseSplitBlockMap]
  · apply denseSplitBlockMap_injective M u
    calc
      denseSplitBlockMap M u (denseSplitFiveTwelve.vertex t j) = Sum.inl s := hj
      _ = denseSplitBlockMap M u (Sum.inl (finFiveEquivZModFive.symm s)) := by
        simp [denseSplitBlockMap]

/-- Within the matching-leave expansion, two distinct residual points can
occur together only in the independent five-point residual packing. -/
private theorem matchingLeaveTriangle_eq_residual_of_covers_two_residual
    (L : TrianglePacking.WithMatchingLeave α) (r s : ZMod 5) (hrs : r ≠ s)
    (t : MatchingLeaveTriangleIndex L)
    (hr : ∃ i : Fin 3, matchingLeaveVertex L t i = Sum.inl r)
    (hs : ∃ j : Fin 3, matchingLeaveVertex L t j = Sum.inl s) :
    ∃ p : Bool, t = Sum.inl p ∧
      (∃ i : Fin 3, fivePointResidualPacking.vertex p i = r) ∧
      ∃ j : Fin 3, fivePointResidualPacking.vertex p j = s := by
  rcases hr with ⟨i, hi⟩
  rcases hs with ⟨j, hj⟩
  cases t with
  | inl p =>
      exact ⟨p, rfl, ⟨i, Sum.inl.inj hi⟩, ⟨j, Sum.inl.inj hj⟩⟩
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨u, t⟩
          exact False.elim
            (denseSplitBlockPacking_not_covers_residual_pair L.matching u r s hrs
              ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩)
      | inr q =>
          fin_cases i <;> simp [matchingLeaveVertex] at hi

/-- A residual-to-group edge is supplied by exactly one matching block; the
macro transversal contains only group vertices. -/
private theorem matchingLeaveTriangle_eq_block_of_covers_residual_group
    (L : TrianglePacking.WithMatchingLeave α) (r : ZMod 5) (a : α) (x : ZMod 6)
    (t : MatchingLeaveTriangleIndex L)
    (hr : ∃ i : Fin 3, matchingLeaveVertex L t i = Sum.inl r)
    (hx : ∃ j : Fin 3, matchingLeaveVertex L t j = Sum.inr (a, x)) :
    ∃ q : MatchingBlockTriangleIndex L.matching, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inl q)) i = Sum.inl r) ∧
      ∃ j : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (a, x) := by
  rcases hr with ⟨i, hi⟩
  rcases hx with ⟨j, hj⟩
  cases t with
  | inl p =>
      fin_cases j <;> simp [matchingLeaveVertex] at hj
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          fin_cases i <;> simp [matchingLeaveVertex] at hi

/-- A pair of distinct points within one macro group can occur only in the
dense-split block attached to that group's matching edge. -/
private theorem matchingLeaveTriangle_eq_block_of_covers_same_group_pair
    (L : TrianglePacking.WithMatchingLeave α) (a : α) (x y : ZMod 6) (hxy : x ≠ y)
    (t : MatchingLeaveTriangleIndex L)
    (hx : ∃ i : Fin 3, matchingLeaveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, matchingLeaveVertex L t j = Sum.inr (a, y)) :
    ∃ q : MatchingBlockTriangleIndex L.matching, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inl q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (a, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p =>
      fin_cases i <;> simp [matchingLeaveVertex] at hi
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          rcases q with ⟨u, p⟩
          have hai : L.packing.vertex u i = a :=
            congrArg Prod.fst (Sum.inr.inj hi)
          have haj : L.packing.vertex u j = a :=
            congrArg Prod.fst (Sum.inr.inj hj)
          have hij : i = j := L.packing.vertex_injective u (hai.trans haj.symm)
          apply False.elim
          apply hxy
          calc
            x = (triplingCrossVertex p i).2 :=
              (congrArg Prod.snd (Sum.inr.inj hi)).symm
            _ = (triplingCrossVertex p j).2 := by rw [hij]
            _ = y := congrArg Prod.snd (Sum.inr.inj hj)

/-- A pair from distinct macro groups that is not a matching edge is supplied
only by the transversal over the macro packing. -/
private theorem matchingLeaveTriangle_eq_transversal_of_covers_nonmatching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 6)
    (hab : a ≠ b) (hnonmatching : L.matching.perm a ≠ b)
    (t : MatchingLeaveTriangleIndex L)
    (hx : ∃ i : Fin 3, matchingLeaveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, matchingLeaveVertex L t j = Sum.inr (b, y)) :
    ∃ q : L.packing.Triangle × (ZMod 6 × ZMod 6), t = Sum.inr (Sum.inr q) ∧
      (∃ i : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inr q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inr q)) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p =>
      fin_cases i <;> simp [matchingLeaveVertex] at hi
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨u, t⟩
          have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
            denseSplitBlockMap_right_macro L.matching u
              (denseSplitFiveTwelve.vertex t i) a x hi
          have hb : b = u.1 ∨ b = L.matching.perm u.1 :=
            denseSplitBlockMap_right_macro L.matching u
              (denseSplitFiveTwelve.vertex t j) b y hj
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact False.elim (hab (ha.trans hb.symm))
          · apply False.elim
            apply hnonmatching
            calc
              L.matching.perm a = L.matching.perm u.1 := by rw [ha]
              _ = b := hb.symm
          · apply False.elim
            apply hnonmatching
            calc
              L.matching.perm a = L.matching.perm (L.matching.perm u.1) := by rw [ha]
              _ = u.1 := L.matching.apply_apply _
              _ = b := hb.symm
          · exact False.elim (hab (ha.trans hb.symm))
      | inr q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩

/-- A matching edge of the macro leave is replaced by its dense-split block;
the macro transversal cannot contain it. -/
private theorem matchingLeaveTriangle_eq_block_of_covers_matching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 6)
    (hab : a ≠ b) (hmatching : L.matching.perm a = b)
    (t : MatchingLeaveTriangleIndex L)
    (hx : ∃ i : Fin 3, matchingLeaveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, matchingLeaveVertex L t j = Sum.inr (b, y)) :
    ∃ q : MatchingBlockTriangleIndex L.matching, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inl q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p =>
      fin_cases i <;> simp [matchingLeaveVertex] at hi
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          rcases q with ⟨u, p⟩
          have hcover : L.packing.CoversPair a b :=
            ⟨u, ⟨i, congrArg Prod.fst (Sum.inr.inj hi)⟩,
              ⟨j, congrArg Prod.fst (Sum.inr.inj hj)⟩⟩
          exact False.elim
            ((L.coversPair_iff a b hab).mp hcover hmatching)

/-- A macro packing and the six-point transversal determine a unique lifted
triangle for every covered pair of distinct macro groups. -/
private theorem matchingLeaveTransversalTriangleIndex_eq_of_distinct_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 6) (hab : a ≠ b)
    (q q' : L.packing.Triangle × (ZMod 6 × ZMod 6))
    (hx : ∃ i : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inr q)) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inr q)) j = Sum.inr (b, y))
    (hx' : ∃ i : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inr q')) i = Sum.inr (a, x))
    (hy' : ∃ j : Fin 3, matchingLeaveVertex L (Sum.inr (Sum.inr q')) j = Sum.inr (b, y)) :
    q = q' := by
  rcases q with ⟨t, p⟩
  rcases q' with ⟨u, p'⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  rcases hx' with ⟨k, hk⟩
  rcases hy' with ⟨l, hl⟩
  have hai : L.packing.vertex t i = a := congrArg Prod.fst (Sum.inr.inj hi)
  have hbj : L.packing.vertex t j = b := congrArg Prod.fst (Sum.inr.inj hj)
  have hak : L.packing.vertex u k = a := congrArg Prod.fst (Sum.inr.inj hk)
  have hbl : L.packing.vertex u l = b := congrArg Prod.fst (Sum.inr.inj hl)
  have hix : (triplingCrossVertex p i).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [matchingLeaveVertex] using hi))
  have hjy : (triplingCrossVertex p j).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [matchingLeaveVertex] using hj))
  have hkx : (triplingCrossVertex p' k).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [matchingLeaveVertex] using hk))
  have hly : (triplingCrossVertex p' l).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [matchingLeaveVertex] using hl))
  have htu : t = u := L.packing.pair_covered_at_most_once a b hab t u
    ⟨i, hai⟩ ⟨j, hbj⟩ ⟨k, hak⟩ ⟨l, hbl⟩
  subst u
  have hik : i = k := L.packing.vertex_injective t (hai.trans hak.symm)
  have hjl : j = l := L.packing.vertex_injective t (hbj.trans hbl.symm)
  subst k
  subst l
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = L.packing.vertex t i := hai.symm
      _ = L.packing.vertex t j := by rw [hij]
      _ = b := hbj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p₀, hp₀, hp₀uniq⟩
  have hp :
      (∃ h : Fin 3, triplingCrossVertex p h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hix
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hjy
  have hp' :
      (∃ h : Fin 3, triplingCrossVertex p' h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p' h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hkx
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hly
  have hpp : p = p' := (hp₀uniq p hp).trans (hp₀uniq p' hp').symm
  subst p'
  rfl

private theorem matchingLeavePacking_pair_covered_at_most_once
    (L : TrianglePacking.WithMatchingLeave α) :
    ∀ x y : ZMod 5 ⊕ (α × ZMod 6), x ≠ y → ∀ t u : MatchingLeaveTriangleIndex L,
      (∃ i : Fin 3, matchingLeaveVertex L t i = x) →
      (∃ j : Fin 3, matchingLeaveVertex L t j = y) →
      (∃ i : Fin 3, matchingLeaveVertex L u i = x) →
      (∃ j : Fin 3, matchingLeaveVertex L u j = y) → t = u := by
  rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hxy t u htx hty hux huy
  · have hrs : r ≠ s := by
      intro hrs
      apply hxy
      rw [hrs]
    rcases matchingLeaveTriangle_eq_residual_of_covers_two_residual L r s hrs t htx hty with
      ⟨p, hp, hpr, hps⟩
    rcases matchingLeaveTriangle_eq_residual_of_covers_two_residual L r s hrs u hux huy with
      ⟨q, hq, hqr, hqs⟩
    calc
      t = Sum.inl p := hp
      _ = Sum.inl q := congrArg Sum.inl
        (fivePointResidualPacking.pair_covered_at_most_once r s hrs p q hpr hps hqr hqs)
      _ = u := hq.symm
  · rcases matchingLeaveTriangle_eq_block_of_covers_residual_group L r b y t htx hty with
      ⟨q, hq, hqr, hqy⟩
    rcases matchingLeaveTriangle_eq_block_of_covers_residual_group L r b y u hux huy with
      ⟨q', hq', hq'r, hq'y⟩
    rcases q with ⟨v, p⟩
    rcases q' with ⟨w, p'⟩
    have hqq' : (⟨v, p⟩ : MatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
      matchingBlockTriangleIndex_eq_of_contains_right_pair L.matching b y (Sum.inl r)
        (by simp) v w p p' hqy hqr hq'y hq'r
    calc
      t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
      _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
      _ = u := hq'.symm
  · rcases matchingLeaveTriangle_eq_block_of_covers_residual_group L s a x t hty htx with
      ⟨q, hq, hqs, hqx⟩
    rcases matchingLeaveTriangle_eq_block_of_covers_residual_group L s a x u huy hux with
      ⟨q', hq', hq's, hq'x⟩
    rcases q with ⟨v, p⟩
    rcases q' with ⟨w, p'⟩
    have hqq' : (⟨v, p⟩ : MatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
      matchingBlockTriangleIndex_eq_of_contains_right_pair L.matching a x (Sum.inl s)
        (by simp) v w p p' hqx hqs hq'x hq's
    calc
      t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
      _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
      _ = u := hq'.symm
  · by_cases hab : a = b
    · subst b
      have hxy' : x ≠ y := by
        intro hxy'
        apply hxy
        simp [hxy']
      rcases matchingLeaveTriangle_eq_block_of_covers_same_group_pair L a x y hxy' t htx hty with
        ⟨q, hq, hqx, hqy⟩
      rcases matchingLeaveTriangle_eq_block_of_covers_same_group_pair L a x y hxy' u hux huy with
        ⟨q', hq', hq'x, hq'y⟩
      rcases q with ⟨v, p⟩
      rcases q' with ⟨w, p'⟩
      have hqq' : (⟨v, p⟩ : MatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
        matchingBlockTriangleIndex_eq_of_contains_right_pair L.matching a x (Sum.inr (a, y))
          hxy v w p p' hqx hqy hq'x hq'y
      calc
        t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
        _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
        _ = u := hq'.symm
    · by_cases hmatching : L.matching.perm a = b
      · rcases matchingLeaveTriangle_eq_block_of_covers_matching_groups
          L a b x y hab hmatching t htx hty with ⟨q, hq, hqx, hqy⟩
        rcases matchingLeaveTriangle_eq_block_of_covers_matching_groups
          L a b x y hab hmatching u hux huy with ⟨q', hq', hq'x, hq'y⟩
        rcases q with ⟨v, p⟩
        rcases q' with ⟨w, p'⟩
        have hqq' : (⟨v, p⟩ : MatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
          matchingBlockTriangleIndex_eq_of_contains_right_pair L.matching a x (Sum.inr (b, y))
            hxy v w p p' hqx hqy hq'x hq'y
        calc
          t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
          _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
          _ = u := hq'.symm
      · rcases matchingLeaveTriangle_eq_transversal_of_covers_nonmatching_groups
          L a b x y hab hmatching t htx hty with ⟨q, hq, hqx, hqy⟩
        rcases matchingLeaveTriangle_eq_transversal_of_covers_nonmatching_groups
          L a b x y hab hmatching u hux huy with ⟨q', hq', hq'x, hq'y⟩
        have hqq' : q = q' :=
          matchingLeaveTransversalTriangleIndex_eq_of_distinct_groups L a b x y hab q q'
            hqx hqy hq'x hq'y
        calc
          t = Sum.inr (Sum.inr q) := hq
          _ = Sum.inr (Sum.inr q') := congrArg (fun z => Sum.inr (Sum.inr z)) hqq'
          _ = u := hq'.symm

/-- Feder--Subi's matching-leave expansion: each macro matching edge is
replaced by the literal dense-split block, while every covered macro triangle
is lifted through the cyclic six-point transversal. -/
noncomputable def matchingLeavePacking
    (L : TrianglePacking.WithMatchingLeave α) : TrianglePacking (ZMod 5 ⊕ (α × ZMod 6)) where
  Triangle := MatchingLeaveTriangleIndex L
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := matchingLeaveVertex L
  vertex_injective := matchingLeaveVertex_injective L
  pair_covered_at_most_once := matchingLeavePacking_pair_covered_at_most_once L

private noncomputable def denseSplitBlockCliqueIndex (M : EvenPairing α)
    (u : MatchingRepresentative M) (a : α) (x : ZMod 6) : Fin 12 :=
  if a = u.1 then finTwelveEquivFinTwoZModSix.symm (0, x)
  else finTwelveEquivFinTwoZModSix.symm (1, x)

private theorem denseSplitBlockMap_cliqueIndex
    (M : EvenPairing α) (u : MatchingRepresentative M) (a : α) (x : ZMod 6)
    (ha : a = u.1 ∨ a = M.perm u.1) :
    denseSplitBlockMap M u (Sum.inr (denseSplitBlockCliqueIndex M u a x)) =
      Sum.inr (a, x) := by
  unfold denseSplitBlockCliqueIndex
  split
  · rename_i h
    simp [denseSplitBlockMap, h]
  · rename_i h
    rcases ha with ha | ha
    · exact False.elim (h ha)
    · simp [denseSplitBlockMap, h, ha]

private theorem denseSplitBlockPacking_covers_residual_group
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (r : ZMod 5) (a : α) (x : ZMod 6)
    (ha : a = u.1 ∨ a = M.perm u.1) :
    (denseSplitBlockPacking M u).CoversPair (Sum.inl r) (Sum.inr (a, x)) := by
  let s := denseSplitBlockCliqueIndex M u a x
  rcases denseSplitBlockPacking_covers_of_base M u
    (denseSplitFiveTwelve_covers_residual_clique (finFiveEquivZModFive.symm r) s) with
      ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  refine ⟨t, ⟨i, hi.trans ?_⟩, ⟨j, hj.trans ?_⟩⟩
  · simp [denseSplitBlockMap]
  · exact denseSplitBlockMap_cliqueIndex M u a x ha

private theorem denseSplitBlockPacking_covers_clique_pair
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (a b : α) (x y : ZMod 6)
    (ha : a = u.1 ∨ a = M.perm u.1)
    (hb : b = u.1 ∨ b = M.perm u.1)
    (hxy : (Sum.inr (a, x) : ZMod 5 ⊕ (α × ZMod 6)) ≠ Sum.inr (b, y)) :
    (denseSplitBlockPacking M u).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  let s := denseSplitBlockCliqueIndex M u a x
  let t := denseSplitBlockCliqueIndex M u b y
  have hst : s ≠ t := by
    intro hst
    apply hxy
    calc
      Sum.inr (a, x) = denseSplitBlockMap M u (Sum.inr s) :=
        (denseSplitBlockMap_cliqueIndex M u a x ha).symm
      _ = denseSplitBlockMap M u (Sum.inr t) := by rw [hst]
      _ = Sum.inr (b, y) := denseSplitBlockMap_cliqueIndex M u b y hb
  rcases denseSplitBlockPacking_covers_of_base M u
    (denseSplitFiveTwelve_covers_clique_pair s t hst) with ⟨q, ⟨i, hi⟩, ⟨j, hj⟩⟩
  exact ⟨q, ⟨i, hi.trans (denseSplitBlockMap_cliqueIndex M u a x ha)⟩,
    ⟨j, hj.trans (denseSplitBlockMap_cliqueIndex M u b y hb)⟩⟩

private theorem matchingLeavePacking_covers_residual_pair_iff
    (L : TrianglePacking.WithMatchingLeave α) (r s : ZMod 5) (hrs : r ≠ s) :
    (matchingLeavePacking L).CoversPair (Sum.inl r) (Sum.inl s) ↔
      fivePointResidualPacking.CoversPair r s := by
  constructor
  · rintro ⟨t, hr, hs⟩
    rcases matchingLeaveTriangle_eq_residual_of_covers_two_residual L r s hrs t hr hs with
      ⟨p, hp, hpr, hps⟩
    exact ⟨p, hpr, hps⟩
  · rintro ⟨p, hr, hs⟩
    rcases hr with ⟨i, hi⟩
    rcases hs with ⟨j, hj⟩
    exact ⟨Sum.inl p, ⟨i, congrArg Sum.inl hi⟩, ⟨j, congrArg Sum.inl hj⟩⟩

private theorem matchingLeavePacking_covers_residual_group
    (L : TrianglePacking.WithMatchingLeave α) (r : ZMod 5) (a : α) (x : ZMod 6) :
    (matchingLeavePacking L).CoversPair (Sum.inl r) (Sum.inr (a, x)) := by
  let u := matchingRepresentative L.matching a
  have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
    matchingRepresentative_endpoints L.matching a
  rcases denseSplitBlockPacking_covers_residual_group L.matching u r a x ha with
    ⟨t, hr, hx⟩
  exact ⟨Sum.inr (Sum.inl ⟨u, t⟩), hr, hx⟩

private theorem matchingLeavePacking_covers_same_group_pair
    (L : TrianglePacking.WithMatchingLeave α) (a : α) (x y : ZMod 6) (hxy : x ≠ y) :
    (matchingLeavePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (a, y)) := by
  let u := matchingRepresentative L.matching a
  have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
    matchingRepresentative_endpoints L.matching a
  have hpair : (Sum.inr (a, x) : ZMod 5 ⊕ (α × ZMod 6)) ≠ Sum.inr (a, y) := by
    intro h
    apply hxy
    exact congrArg Prod.snd (Sum.inr.inj h)
  rcases denseSplitBlockPacking_covers_clique_pair L.matching u a a x y ha ha hpair with
    ⟨t, hx, hy⟩
  exact ⟨Sum.inr (Sum.inl ⟨u, t⟩), hx, hy⟩

private theorem matchingLeavePacking_covers_matching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 6)
    (hab : a ≠ b) (hmatching : L.matching.perm a = b) :
    (matchingLeavePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  let u := matchingRepresentative L.matching a
  have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
    matchingRepresentative_endpoints L.matching a
  have hb : b = u.1 ∨ b = L.matching.perm u.1 := by
    rcases ha with ha | ha
    · right
      calc
        b = L.matching.perm a := hmatching.symm
        _ = L.matching.perm u.1 := by rw [ha]
    · left
      calc
        b = L.matching.perm a := hmatching.symm
        _ = L.matching.perm (L.matching.perm u.1) := by rw [ha]
        _ = u.1 := L.matching.apply_apply _
  have hpair : (Sum.inr (a, x) : ZMod 5 ⊕ (α × ZMod 6)) ≠ Sum.inr (b, y) := by
    intro h
    apply hab
    exact congrArg Prod.fst (Sum.inr.inj h)
  rcases denseSplitBlockPacking_covers_clique_pair L.matching u a b x y ha hb hpair with
    ⟨t, hx, hy⟩
  exact ⟨Sum.inr (Sum.inl ⟨u, t⟩), hx, hy⟩

private theorem matchingLeavePacking_covers_nonmatching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 6)
    (hab : a ≠ b) (hnonmatching : L.matching.perm a ≠ b) :
    (matchingLeavePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  rcases (L.coversPair_iff a b hab).mpr hnonmatching with ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = L.packing.vertex t i := hi.symm
      _ = L.packing.vertex t j := by rw [hij]
      _ = b := hj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p, hp, hpuniq⟩
  rcases hp with ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hki : k = i := triplingCrossVertex_index_eq_fst hk
  have hlj : l = j := triplingCrossVertex_index_eq_fst hl
  subst k
  subst l
  refine ⟨Sum.inr (Sum.inr (t, p)), ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · change Sum.inr (L.packing.vertex t i, (triplingCrossVertex p i).2) = Sum.inr (a, x)
    apply congrArg Sum.inr
    have hoffset : (triplingCrossVertex p i).2 = x := congrArg Prod.snd hk
    rw [hi, hoffset]
  · change Sum.inr (L.packing.vertex t j, (triplingCrossVertex p j).2) = Sum.inr (b, y)
    apply congrArg Sum.inr
    have hoffset : (triplingCrossVertex p j).2 = y := congrArg Prod.snd hl
    rw [hj, hoffset]

/-- Feder--Subi's matching-leave expansion leaves precisely the four-cycle in
the common five-point residual set. -/
theorem matchingLeavePacking_leavesFourCycle
    (L : TrianglePacking.WithMatchingLeave α) :
    (matchingLeavePacking L).LeavesFourCycle (sixGroupLeaveVertex (α := α)) := by
  constructor
  · intro i j hij
    apply fivePointResidualPacking_leavesFourCycle.1
    exact Sum.inl.inj hij
  · rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hxy
    · have hrs : r ≠ s := by
        intro hrs
        apply hxy
        rw [hrs]
      constructor
      · intro hcover
        have hbase : fivePointResidualPacking.CoversPair r s :=
          (matchingLeavePacking_covers_residual_pair_iff L r s hrs).mp hcover
        have hnotbase : ¬ ∃ i : Fin 4, s(r, s) =
            s(fivePointResidualLeaveVertex i, fivePointResidualLeaveVertex (fourCycleNext i)) :=
          (fivePointResidualPacking_leavesFourCycle.2 r s hrs).mp hbase
        intro hcycle
        apply hnotbase
        exact (sixGroupLeave_cycle_iff (α := α) r s).mp hcycle
      · intro hnotcycle
        apply (matchingLeavePacking_covers_residual_pair_iff L r s hrs).mpr
        apply (fivePointResidualPacking_leavesFourCycle.2 r s hrs).mpr
        intro hbasecycle
        apply hnotcycle
        exact (sixGroupLeave_cycle_iff (α := α) r s).mpr hbasecycle
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨_, hright⟩ | ⟨_, hright⟩
        · simp [sixGroupLeaveVertex] at hright
        · simp [sixGroupLeaveVertex] at hright
      · intro hnotcycle
        exact matchingLeavePacking_covers_residual_group L r b y
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [sixGroupLeaveVertex] at hleft
        · simp [sixGroupLeaveVertex] at hleft
      · intro hnotcycle
        rcases matchingLeavePacking_covers_residual_group L s a x with ⟨t, hs, ha⟩
        exact ⟨t, ha, hs⟩
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [sixGroupLeaveVertex] at hleft
        · simp [sixGroupLeaveVertex] at hleft
      · intro hnotcycle
        by_cases hab : a = b
        · subst b
          have hxy' : x ≠ y := by
            intro hxy'
            apply hxy
            simp [hxy']
          exact matchingLeavePacking_covers_same_group_pair L a x y hxy'
        · by_cases hmatching : L.matching.perm a = b
          · exact matchingLeavePacking_covers_matching_groups L a b x y hab hmatching
          · exact matchingLeavePacking_covers_nonmatching_groups L a b x y hab hmatching

/-- Standard finite-label form of the matching-leave expansion.  An
`STS(m+1)` first supplies the macro packing with a perfect-matching leave by
center removal, then the construction produces a packing on `6m+5` points. -/
noncomputable def matchingLeavePackingFin
    (S : SteinerTripleSystem (Fin (m + 1))) : TrianglePacking (Fin (6 * m + 5)) := by
  let e : ZMod 5 ⊕ (Fin m × ZMod 6) ≃ Fin (6 * m + 5) :=
    Fintype.equivFinOfCardEq (card_sixGroupCarrier m)
  exact (matchingLeavePacking (centerRemovedWithMatchingLeaveFin S)).map e

/-- The source's Feder--Subi `m ≡ 0,2 (mod 6)` group-six case: the required
macro `STS(m+1)` exists, and its matching leave is expanded into literal
five-plus-twelve dense-split blocks. -/
theorem exists_matchingLeavePackingFin_leavesFourCycle_of_modSix
    (m : ℕ) (hm : m % 6 = 0 ∨ m % 6 = 2) :
    ∃ v : Fin 4 → Fin (6 * m + 5),
      (matchingLeavePackingFin (m := m)
        (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (m + 1) (by
          rcases hm with hm | hm <;> omega)).some).LeavesFourCycle v := by
  let S : SteinerTripleSystem (Fin (m + 1)) :=
    (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (m + 1) (by
      rcases hm with hm | hm <;> omega)).some
  let e : ZMod 5 ⊕ (Fin m × ZMod 6) ≃ Fin (6 * m + 5) :=
    Fintype.equivFinOfCardEq (card_sixGroupCarrier m)
  refine ⟨e ∘ sixGroupLeaveVertex, ?_⟩
  exact TrianglePacking.map_leavesFourCycle e
    (matchingLeavePacking (centerRemovedWithMatchingLeaveFin S)) sixGroupLeaveVertex
    (matchingLeavePacking_leavesFourCycle (centerRemovedWithMatchingLeaveFin S))

end DenseSplitBlocks

section ThreePointMatchingBlocks

/-- The `r=5,t=0` split block from Feder--Subi: a five-point residual side
and a six-point clique whose Walecki factors supply the residual triangles.
Unlike the 17-point dense-split block, its clique has no internal triangles. -/
private abbrev SixPointSplitTriangle :=
  Sigma fun r : ZMod 5 => SixPointMatchingRepresentative r

private noncomputable def sixPointSplitVertex : SixPointSplitTriangle → Fin 3 → ZMod 5 ⊕ ZMod 6
  | ⟨r, u⟩ => fun i =>
      if i = 0 then Sum.inl r
      else if i = 1 then Sum.inr u.1
      else Sum.inr ((sixPointGroupFactorization.matching r).perm u.1)

private theorem sixPointSplitVertex_injective (t : SixPointSplitTriangle) :
    Function.Injective (sixPointSplitVertex t) := by
  rcases t with ⟨r, u⟩
  intro i j hij
  fin_cases i
  · fin_cases j
    · rfl
    · simp [sixPointSplitVertex] at hij
    · simp [sixPointSplitVertex] at hij
  · fin_cases j
    · simp [sixPointSplitVertex] at hij
    · rfl
    · have hpartner : u.1 = (sixPointGroupFactorization.matching r).perm u.1 :=
        by simpa [sixPointSplitVertex] using hij
      exact False.elim ((sixPointGroupFactorization.matching r).apply_ne u.1 hpartner.symm)
  · fin_cases j
    · simp [sixPointSplitVertex] at hij
    · have hpartner : (sixPointGroupFactorization.matching r).perm u.1 = u.1 :=
        by simpa [sixPointSplitVertex] using hij
      exact False.elim ((sixPointGroupFactorization.matching r).apply_ne u.1 hpartner)
    · rfl

private theorem sixPointSplitTriangle_eq_of_residual_group
    (r : ZMod 5) (x : ZMod 6) (q : SixPointSplitTriangle)
    (hr : ∃ i : Fin 3, sixPointSplitVertex q i = Sum.inl r)
    (hx : ∃ j : Fin 3, sixPointSplitVertex q j = Sum.inr x) :
    q = ⟨r, sixPointMatchingRepresentative r x⟩ := by
  rcases q with ⟨r', u⟩
  rcases hr with ⟨i, hi⟩
  fin_cases i
  · change Sum.inl r' = Sum.inl r at hi
    have hr' : r' = r := Sum.inl.inj hi
    subst r'
    rcases hx with ⟨j, hj⟩
    fin_cases j
    · simp [sixPointSplitVertex] at hj
    · change Sum.inr u.1 = Sum.inr x at hj
      have hu : u.1 = x := Sum.inr.inj hj
      have hrep : sixPointMatchingRepresentative r x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint r u x (Or.inl hu.symm)
      rw [hrep]
    · change Sum.inr ((sixPointGroupFactorization.matching r).perm u.1) = Sum.inr x at hj
      have hu : (sixPointGroupFactorization.matching r).perm u.1 = x := Sum.inr.inj hj
      have hrep : sixPointMatchingRepresentative r x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint r u x (Or.inr hu.symm)
      rw [hrep]
  · simp [sixPointSplitVertex] at hi
  · simp [sixPointSplitVertex] at hi

private theorem sixPointSplitTriangle_eq_of_clique_pair
    (x y : ZMod 6) (hxy : x ≠ y) (q : SixPointSplitTriangle)
    (hx : ∃ i : Fin 3, sixPointSplitVertex q i = Sum.inr x)
    (hy : ∃ j : Fin 3, sixPointSplitVertex q j = Sum.inr y) :
    q = ⟨sixPointGroupFactorization.factorOfPair x y hxy,
      sixPointMatchingRepresentative (sixPointGroupFactorization.factorOfPair x y hxy) x⟩ := by
  rcases q with ⟨r, u⟩
  rcases hx with ⟨i, hi⟩
  fin_cases i
  · simp [sixPointSplitVertex] at hi
  · change Sum.inr u.1 = Sum.inr x at hi
    have hu : u.1 = x := Sum.inr.inj hi
    rcases hy with ⟨j, hj⟩
    fin_cases j
    · simp [sixPointSplitVertex] at hj
    · change Sum.inr u.1 = Sum.inr y at hj
      exact False.elim (hxy (hu.symm.trans (Sum.inr.inj hj)))
    · change Sum.inr ((sixPointGroupFactorization.matching r).perm u.1) = Sum.inr y at hj
      have hmatch_u : (sixPointGroupFactorization.matching r).perm u.1 = y :=
        Sum.inr.inj hj
      have hmatch : (sixPointGroupFactorization.matching r).perm x = y := by
        rw [← hu]
        exact hmatch_u
      have hr : r = sixPointGroupFactorization.factorOfPair x y hxy :=
        sixPointGroupFactorization.factorOfPair_eq_of_matching hxy r hmatch
      subst r
      have hrep : sixPointMatchingRepresentative
          (sixPointGroupFactorization.factorOfPair x y hxy) x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint _ u x (Or.inl hu.symm)
      rw [hrep]
  · change Sum.inr ((sixPointGroupFactorization.matching r).perm u.1) = Sum.inr x at hi
    have hmatch_u : (sixPointGroupFactorization.matching r).perm u.1 = x := Sum.inr.inj hi
    rcases hy with ⟨j, hj⟩
    fin_cases j
    · simp [sixPointSplitVertex] at hj
    · change Sum.inr u.1 = Sum.inr y at hj
      have hu : u.1 = y := Sum.inr.inj hj
      have hmatch : (sixPointGroupFactorization.matching r).perm x = y := by
        calc
          (sixPointGroupFactorization.matching r).perm x =
              (sixPointGroupFactorization.matching r).perm
                ((sixPointGroupFactorization.matching r).perm u.1) := by rw [hmatch_u]
          _ = u.1 := (sixPointGroupFactorization.matching r).apply_apply u.1
          _ = y := hu
      have hr : r = sixPointGroupFactorization.factorOfPair x y hxy :=
        sixPointGroupFactorization.factorOfPair_eq_of_matching hxy r hmatch
      subst r
      have hrep : sixPointMatchingRepresentative
          (sixPointGroupFactorization.factorOfPair x y hxy) x = u :=
        sixPointMatchingRepresentative_eq_of_endpoint _ u x (Or.inr hmatch_u.symm)
      rw [hrep]
    · change Sum.inr ((sixPointGroupFactorization.matching r).perm u.1) = Sum.inr y at hj
      exact False.elim
        (hxy (hmatch_u.symm.trans (Sum.inr.inj hj)))

private theorem sixPointSplitPacking_pair_covered_at_most_once :
    ∀ x y : ZMod 5 ⊕ ZMod 6, x ≠ y → ∀ t u : SixPointSplitTriangle,
      (∃ i : Fin 3, sixPointSplitVertex t i = x) →
      (∃ j : Fin 3, sixPointSplitVertex t j = y) →
      (∃ i : Fin 3, sixPointSplitVertex u i = x) →
      (∃ j : Fin 3, sixPointSplitVertex u j = y) → t = u := by
  rintro (r | x) (s | y) hxy t u htx hty hux huy
  · rcases t with ⟨r', p⟩
    rcases htx with ⟨i, hi⟩
    rcases hty with ⟨j, hj⟩
    have hir : r' = r := by
      fin_cases i
      · exact Sum.inl.inj hi
      · simp [sixPointSplitVertex] at hi
      · simp [sixPointSplitVertex] at hi
    have hjs : r' = s := by
      fin_cases j
      · exact Sum.inl.inj hj
      · simp [sixPointSplitVertex] at hj
      · simp [sixPointSplitVertex] at hj
    exact False.elim (hxy (by rw [← hir, hjs]))
  · have hcanon : t = ⟨r, sixPointMatchingRepresentative r y⟩ :=
      sixPointSplitTriangle_eq_of_residual_group r y t htx hty
    have hcanon' : u = ⟨r, sixPointMatchingRepresentative r y⟩ :=
      sixPointSplitTriangle_eq_of_residual_group r y u hux huy
    exact hcanon.trans hcanon'.symm
  · have hcanon : t = ⟨s, sixPointMatchingRepresentative s x⟩ :=
      sixPointSplitTriangle_eq_of_residual_group s x t hty htx
    have hcanon' : u = ⟨s, sixPointMatchingRepresentative s x⟩ :=
      sixPointSplitTriangle_eq_of_residual_group s x u huy hux
    exact hcanon.trans hcanon'.symm
  · have hxy' : x ≠ y := by
      intro hxy'
      apply hxy
      simp [hxy']
    have hcanon : t = ⟨sixPointGroupFactorization.factorOfPair x y hxy',
        sixPointMatchingRepresentative (sixPointGroupFactorization.factorOfPair x y hxy') x⟩ :=
      sixPointSplitTriangle_eq_of_clique_pair x y hxy' t htx hty
    have hcanon' : u = ⟨sixPointGroupFactorization.factorOfPair x y hxy',
        sixPointMatchingRepresentative (sixPointGroupFactorization.factorOfPair x y hxy') x⟩ :=
      sixPointSplitTriangle_eq_of_clique_pair x y hxy' u hux huy
    exact hcanon.trans hcanon'.symm

private noncomputable def sixPointSplitPacking : TrianglePacking (ZMod 5 ⊕ ZMod 6) where
  Triangle := SixPointSplitTriangle
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := sixPointSplitVertex
  vertex_injective := sixPointSplitVertex_injective
  pair_covered_at_most_once := sixPointSplitPacking_pair_covered_at_most_once

private theorem sixPointSplitPacking_covers_residual_clique
    (r : ZMod 5) (x : ZMod 6) :
    sixPointSplitPacking.CoversPair (Sum.inl r) (Sum.inr x) := by
  refine ⟨⟨r, sixPointMatchingRepresentative r x⟩, ⟨0, rfl⟩, ?_⟩
  rcases sixPointMatchingRepresentative_endpoints r x with hx | hx
  · exact ⟨1, congrArg Sum.inr hx.symm⟩
  · exact ⟨2, congrArg Sum.inr hx.symm⟩

private theorem sixPointSplitPacking_covers_clique_pair
    (x y : ZMod 6) (hxy : x ≠ y) :
    sixPointSplitPacking.CoversPair (Sum.inr x) (Sum.inr y) := by
  let r := sixPointGroupFactorization.factorOfPair x y hxy
  have hmatch : (sixPointGroupFactorization.matching r).perm x = y :=
    sixPointGroupFactorization.matching_factorOfPair x y hxy
  refine ⟨⟨r, sixPointMatchingRepresentative r x⟩, ?_, ?_⟩
  · rcases sixPointMatchingRepresentative_endpoints r x with hx | hx
    · exact ⟨1, congrArg Sum.inr hx.symm⟩
    · exact ⟨2, congrArg Sum.inr hx.symm⟩
  · have hrep : sixPointMatchingRepresentative r y = sixPointMatchingRepresentative r x := by
      rcases sixPointMatchingRepresentative_endpoints r x with hx | hx
      · apply sixPointMatchingRepresentative_eq_of_endpoint r
          (sixPointMatchingRepresentative r x) y
        right
        calc
          y = (sixPointGroupFactorization.matching r).perm x := hmatch.symm
          _ = (sixPointGroupFactorization.matching r).perm
            (sixPointMatchingRepresentative r x).1 := congrArg _ hx
      · apply sixPointMatchingRepresentative_eq_of_endpoint r
          (sixPointMatchingRepresentative r x) y
        left
        calc
          y = (sixPointGroupFactorization.matching r).perm x := hmatch.symm
          _ = (sixPointGroupFactorization.matching r).perm
            ((sixPointGroupFactorization.matching r).perm
              (sixPointMatchingRepresentative r x).1) := congrArg _ hx
          _ = (sixPointMatchingRepresentative r x).1 :=
            (sixPointGroupFactorization.matching r).apply_apply _
    rcases sixPointMatchingRepresentative_endpoints r y with hy | hy
    · refine ⟨1, ?_⟩
      change Sum.inr (sixPointMatchingRepresentative r x).1 = Sum.inr y
      rw [← hrep]
      exact congrArg Sum.inr hy.symm
    · refine ⟨2, ?_⟩
      change Sum.inr ((sixPointGroupFactorization.matching r).perm
        (sixPointMatchingRepresentative r x).1) = Sum.inr y
      rw [← hrep]
      exact congrArg Sum.inr hy.symm

private theorem sixPointSplitPacking_not_covers_residual_pair
    (r s : ZMod 5) (hrs : r ≠ s) :
    ¬ sixPointSplitPacking.CoversPair (Sum.inl r) (Sum.inl s) := by
  rintro ⟨⟨r', u⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩
  change sixPointSplitVertex ⟨r', u⟩ i = Sum.inl r at hi
  change sixPointSplitVertex ⟨r', u⟩ j = Sum.inl s at hj
  have hir : r' = r := by
    fin_cases i
    · exact Sum.inl.inj hi
    · simp [sixPointSplitVertex] at hi
    · simp [sixPointSplitVertex] at hi
  have hjs : r' = s := by
    fin_cases j
    · exact Sum.inl.inj hj
    · simp [sixPointSplitVertex] at hj
    · simp [sixPointSplitVertex] at hj
  exact hrs (hir.symm.trans hjs)

section ThreePointMacroExpansion

open AppliedModelingLib.Foundations.Graph

/-- A fixed grouping of six points into two three-point fibres. -/
private noncomputable def zModSixEquivFinTwoZModThree : ZMod 6 ≃ Fin 2 × ZMod 3 := by
  let e1 : ZMod 6 ≃ Fin 6 := Fintype.equivFinOfCardEq (by norm_num [ZMod.card])
  let e2 : Fin 2 × ZMod 3 ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by norm_num [Fintype.card_prod, ZMod.card])
  exact e1.trans e2.symm

/-- Embed the six-clique split block on a selected matching edge between two
three-point macro groups. -/
private noncomputable def threePointBlockMap (M : EvenPairing α)
    (u : MatchingRepresentative M) : ZMod 5 ⊕ ZMod 6 → ZMod 5 ⊕ (α × ZMod 3)
  | Sum.inl r => Sum.inl r
  | Sum.inr z =>
      let q := zModSixEquivFinTwoZModThree z
      if q.1 = 0 then Sum.inr (u.1, q.2)
      else Sum.inr (M.perm u.1, q.2)

private noncomputable def threePointBlockRetract (M : EvenPairing α)
    (u : MatchingRepresentative M) : ZMod 5 ⊕ (α × ZMod 3) → ZMod 5 ⊕ ZMod 6
  | Sum.inl r => Sum.inl r
  | Sum.inr (a, x) =>
      if a = u.1 then Sum.inr (zModSixEquivFinTwoZModThree.symm (0, x))
      else Sum.inr (zModSixEquivFinTwoZModThree.symm (1, x))

private theorem threePointBlockRetract_apply (M : EvenPairing α)
    (u : MatchingRepresentative M) :
    Function.LeftInverse (threePointBlockRetract M u) (threePointBlockMap M u) := by
  intro z
  cases z with
  | inl r => simp [threePointBlockMap, threePointBlockRetract]
  | inr z =>
      cases hz : zModSixEquivFinTwoZModThree z with
      | mk g x =>
          fin_cases g
          · simp [threePointBlockMap, threePointBlockRetract, hz]
            apply zModSixEquivFinTwoZModThree.injective
            simpa using hz.symm
          · have hne : M.perm u.1 ≠ u.1 := M.apply_ne u.1
            simp [threePointBlockMap, threePointBlockRetract, hz, hne]
            apply zModSixEquivFinTwoZModThree.injective
            simpa using hz.symm

private theorem threePointBlockMap_injective (M : EvenPairing α)
    (u : MatchingRepresentative M) : Function.Injective (threePointBlockMap M u) :=
  (threePointBlockRetract_apply M u).injective

private noncomputable def threePointBlockVertex (M : EvenPairing α)
    (u : MatchingRepresentative M) (t : SixPointSplitTriangle) (i : Fin 3) :
    ZMod 5 ⊕ (α × ZMod 3) :=
  threePointBlockMap M u (sixPointSplitVertex t i)

private theorem threePointBlockVertex_injective (M : EvenPairing α)
    (u : MatchingRepresentative M) (t : SixPointSplitTriangle) :
    Function.Injective (threePointBlockVertex M u t) :=
  (threePointBlockMap_injective M u).comp (sixPointSplitVertex_injective t)

private noncomputable def threePointBlockPacking (M : EvenPairing α)
    (u : MatchingRepresentative M) : TrianglePacking (ZMod 5 ⊕ (α × ZMod 3)) where
  Triangle := SixPointSplitTriangle
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := inferInstance
  vertex := threePointBlockVertex M u
  vertex_injective := threePointBlockVertex_injective M u
  pair_covered_at_most_once := by
    intro x y hxy t q htx hty hqx hqy
    rcases htx with ⟨i, hi⟩
    rcases hty with ⟨j, hj⟩
    rcases hqx with ⟨k, hk⟩
    rcases hqy with ⟨l, hl⟩
    apply sixPointSplitPacking.pair_covered_at_most_once
      (sixPointSplitVertex t i) (sixPointSplitVertex t j) (by
        intro hij
        apply hxy
        calc
          x = threePointBlockMap M u (sixPointSplitVertex t i) := hi.symm
          _ = threePointBlockMap M u (sixPointSplitVertex t j) := by rw [hij]
          _ = y := hj) t q
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
    · refine ⟨k, ?_⟩
      apply threePointBlockMap_injective M u
      calc
        threePointBlockMap M u (sixPointSplitVertex q k) = x := hk
        _ = threePointBlockMap M u (sixPointSplitVertex t i) := hi.symm
    · refine ⟨l, ?_⟩
      apply threePointBlockMap_injective M u
      calc
        threePointBlockMap M u (sixPointSplitVertex q l) = y := hl
        _ = threePointBlockMap M u (sixPointSplitVertex t j) := hj.symm

private theorem threePointBlockPacking_not_covers_residual_pair
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (r s : ZMod 5) (hrs : r ≠ s) :
    ¬ (threePointBlockPacking M u).CoversPair (Sum.inl r) (Sum.inl s) := by
  rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  apply sixPointSplitPacking_not_covers_residual_pair r s hrs
  refine ⟨t, ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · apply threePointBlockMap_injective M u
    exact hi
  · apply threePointBlockMap_injective M u
    exact hj

private theorem threePointBlockMap_right_macro
    (M : EvenPairing α) (u : MatchingRepresentative M) (z : ZMod 5 ⊕ ZMod 6)
    (a : α) (x : ZMod 3)
    (h : threePointBlockMap M u z = Sum.inr (a, x)) :
    a = u.1 ∨ a = M.perm u.1 := by
  cases z with
  | inl r => simp [threePointBlockMap] at h
  | inr z =>
      let q := zModSixEquivFinTwoZModThree z
      by_cases hq : q.1 = 0
      · left
        have hpair : (u.1, q.2) = (a, x) := by
          simpa [threePointBlockMap, q, hq] using h
        exact (congrArg Prod.fst hpair).symm
      · right
        have hpair : (M.perm u.1, q.2) = (a, x) := by
          simpa [threePointBlockMap, q, hq] using h
        exact (congrArg Prod.fst hpair).symm

private theorem threePointBlockRepresentative_eq_of_contains
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (t : SixPointSplitTriangle) (a : α) (x : ZMod 3)
    (h : ∃ i : Fin 3, threePointBlockVertex M u t i = Sum.inr (a, x)) :
    u = matchingRepresentative M a := by
  rcases h with ⟨i, hi⟩
  apply (matchingRepresentative_eq_of_endpoint M u a
    (threePointBlockMap_right_macro M u (sixPointSplitVertex t i) a x hi)).symm

private abbrev ThreePointMatchingBlockTriangleIndex (M : EvenPairing α) :=
  Sigma fun u : MatchingRepresentative M => SixPointSplitTriangle

private theorem threePointMatchingBlockTriangleIndex_eq_of_contains_right_pair
    (M : EvenPairing α) (a : α) (x : ZMod 3)
    (y : ZMod 5 ⊕ (α × ZMod 3))
    (hxy : Sum.inr (a, x) ≠ y)
    (u v : MatchingRepresentative M) (t q : SixPointSplitTriangle)
    (htx : ∃ i : Fin 3, threePointBlockVertex M u t i = Sum.inr (a, x))
    (hty : ∃ j : Fin 3, threePointBlockVertex M u t j = y)
    (hqx : ∃ i : Fin 3, threePointBlockVertex M v q i = Sum.inr (a, x))
    (hqy : ∃ j : Fin 3, threePointBlockVertex M v q j = y) :
    (⟨u, t⟩ : ThreePointMatchingBlockTriangleIndex M) = ⟨v, q⟩ := by
  have hu : u = matchingRepresentative M a :=
    threePointBlockRepresentative_eq_of_contains M u t a x htx
  have hv : v = matchingRepresentative M a :=
    threePointBlockRepresentative_eq_of_contains M v q a x hqx
  subst u
  subst v
  congr 1
  exact (threePointBlockPacking M (matchingRepresentative M a)).pair_covered_at_most_once
    (Sum.inr (a, x)) y hxy t q htx hty hqx hqy

private abbrev ThreePointMatchingLeaveTriangleIndex
    (L : TrianglePacking.WithMatchingLeave α) :=
  Bool ⊕ (ThreePointMatchingBlockTriangleIndex L.matching ⊕
    (L.packing.Triangle × (ZMod 3 × ZMod 3)))

private noncomputable def threePointMatchingLeaveVertex
    (L : TrianglePacking.WithMatchingLeave α) :
    ThreePointMatchingLeaveTriangleIndex L → Fin 3 → ZMod 5 ⊕ (α × ZMod 3)
  | Sum.inl p => fun i => Sum.inl (fivePointResidualPacking.vertex p i)
  | Sum.inr (Sum.inl ⟨u, t⟩) => threePointBlockVertex L.matching u t
  | Sum.inr (Sum.inr (t, p)) => fun i =>
      Sum.inr (L.packing.vertex t i, (triplingCrossVertex p i).2)

private theorem threePointMatchingLeaveVertex_injective
    (L : TrianglePacking.WithMatchingLeave α) (t : ThreePointMatchingLeaveTriangleIndex L) :
    Function.Injective (threePointMatchingLeaveVertex L t) := by
  cases t with
  | inl p =>
      intro i j hij
      apply fivePointResidualPacking.vertex_injective p
      exact Sum.inl.inj hij
  | inr t =>
      cases t with
      | inl q =>
          rcases q with ⟨u, t⟩
          exact threePointBlockVertex_injective L.matching u t
      | inr q =>
          rcases q with ⟨t, p⟩
          intro i j hij
          apply L.packing.vertex_injective t
          exact congrArg (fun q : α × ZMod 3 => q.1) (Sum.inr.inj hij)

private theorem threePointMatchingLeaveTriangle_eq_residual_of_covers_two_residual
    (L : TrianglePacking.WithMatchingLeave α) (r s : ZMod 5) (hrs : r ≠ s)
    (t : ThreePointMatchingLeaveTriangleIndex L)
    (hr : ∃ i : Fin 3, threePointMatchingLeaveVertex L t i = Sum.inl r)
    (hs : ∃ j : Fin 3, threePointMatchingLeaveVertex L t j = Sum.inl s) :
    ∃ p : Bool, t = Sum.inl p ∧
      (∃ i : Fin 3, fivePointResidualPacking.vertex p i = r) ∧
      ∃ j : Fin 3, fivePointResidualPacking.vertex p j = s := by
  rcases hr with ⟨i, hi⟩
  rcases hs with ⟨j, hj⟩
  cases t with
  | inl p => exact ⟨p, rfl, ⟨i, Sum.inl.inj hi⟩, ⟨j, Sum.inl.inj hj⟩⟩
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨u, t⟩
          exact False.elim
            (threePointBlockPacking_not_covers_residual_pair L.matching u r s hrs
              ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩)
      | inr q =>
          fin_cases i <;> simp [threePointMatchingLeaveVertex] at hi

private theorem threePointMatchingLeaveTriangle_eq_block_of_covers_residual_group
    (L : TrianglePacking.WithMatchingLeave α) (r : ZMod 5) (a : α) (x : ZMod 3)
    (t : ThreePointMatchingLeaveTriangleIndex L)
    (hr : ∃ i : Fin 3, threePointMatchingLeaveVertex L t i = Sum.inl r)
    (hx : ∃ j : Fin 3, threePointMatchingLeaveVertex L t j = Sum.inr (a, x)) :
    ∃ q : ThreePointMatchingBlockTriangleIndex L.matching, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inl q)) i = Sum.inl r) ∧
      ∃ j : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (a, x) := by
  rcases hr with ⟨i, hi⟩
  rcases hx with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases j <;> simp [threePointMatchingLeaveVertex] at hj
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q => fin_cases i <;> simp [threePointMatchingLeaveVertex] at hi

private theorem threePointMatchingLeaveTriangle_eq_block_of_covers_same_group_pair
    (L : TrianglePacking.WithMatchingLeave α) (a : α) (x y : ZMod 3) (hxy : x ≠ y)
    (t : ThreePointMatchingLeaveTriangleIndex L)
    (hx : ∃ i : Fin 3, threePointMatchingLeaveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, threePointMatchingLeaveVertex L t j = Sum.inr (a, y)) :
    ∃ q : ThreePointMatchingBlockTriangleIndex L.matching, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inl q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (a, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases i <;> simp [threePointMatchingLeaveVertex] at hi
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          rcases q with ⟨u, p⟩
          have hai : L.packing.vertex u i = a :=
            congrArg Prod.fst (Sum.inr.inj hi)
          have haj : L.packing.vertex u j = a :=
            congrArg Prod.fst (Sum.inr.inj hj)
          have hij : i = j := L.packing.vertex_injective u (hai.trans haj.symm)
          apply False.elim
          apply hxy
          calc
            x = (triplingCrossVertex p i).2 :=
              (congrArg Prod.snd (Sum.inr.inj hi)).symm
            _ = (triplingCrossVertex p j).2 := by rw [hij]
            _ = y := congrArg Prod.snd (Sum.inr.inj hj)

private theorem threePointMatchingLeaveTriangle_eq_transversal_of_covers_nonmatching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hnonmatching : L.matching.perm a ≠ b)
    (t : ThreePointMatchingLeaveTriangleIndex L)
    (hx : ∃ i : Fin 3, threePointMatchingLeaveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, threePointMatchingLeaveVertex L t j = Sum.inr (b, y)) :
    ∃ q : L.packing.Triangle × (ZMod 3 × ZMod 3), t = Sum.inr (Sum.inr q) ∧
      (∃ i : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inr q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inr q)) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases i <;> simp [threePointMatchingLeaveVertex] at hi
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨u, t⟩
          have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
            threePointBlockMap_right_macro L.matching u (sixPointSplitVertex t i) a x hi
          have hb : b = u.1 ∨ b = L.matching.perm u.1 :=
            threePointBlockMap_right_macro L.matching u (sixPointSplitVertex t j) b y hj
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact False.elim (hab (ha.trans hb.symm))
          · apply False.elim
            apply hnonmatching
            calc
              L.matching.perm a = L.matching.perm u.1 := by rw [ha]
              _ = b := hb.symm
          · apply False.elim
            apply hnonmatching
            calc
              L.matching.perm a = L.matching.perm (L.matching.perm u.1) := by rw [ha]
              _ = u.1 := L.matching.apply_apply _
              _ = b := hb.symm
          · exact False.elim (hab (ha.trans hb.symm))
      | inr q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩

private theorem threePointMatchingLeaveTriangle_eq_block_of_covers_matching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hmatching : L.matching.perm a = b)
    (t : ThreePointMatchingLeaveTriangleIndex L)
    (hx : ∃ i : Fin 3, threePointMatchingLeaveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, threePointMatchingLeaveVertex L t j = Sum.inr (b, y)) :
    ∃ q : ThreePointMatchingBlockTriangleIndex L.matching, t = Sum.inr (Sum.inl q) ∧
      (∃ i : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inl q)) i = Sum.inr (a, x)) ∧
      ∃ j : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases i <;> simp [threePointMatchingLeaveVertex] at hi
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          rcases q with ⟨u, p⟩
          have hcover : L.packing.CoversPair a b :=
            ⟨u, ⟨i, congrArg Prod.fst (Sum.inr.inj hi)⟩,
              ⟨j, congrArg Prod.fst (Sum.inr.inj hj)⟩⟩
          exact False.elim ((L.coversPair_iff a b hab).mp hcover hmatching)

private theorem threePointMatchingLeaveTransversalTriangleIndex_eq_of_distinct_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 3) (hab : a ≠ b)
    (q q' : L.packing.Triangle × (ZMod 3 × ZMod 3))
    (hx : ∃ i : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inr q)) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inr q)) j = Sum.inr (b, y))
    (hx' : ∃ i : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inr q')) i = Sum.inr (a, x))
    (hy' : ∃ j : Fin 3, threePointMatchingLeaveVertex L (Sum.inr (Sum.inr q')) j = Sum.inr (b, y)) :
    q = q' := by
  rcases q with ⟨t, p⟩
  rcases q' with ⟨u, p'⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  rcases hx' with ⟨k, hk⟩
  rcases hy' with ⟨l, hl⟩
  have hai : L.packing.vertex t i = a := congrArg Prod.fst (Sum.inr.inj hi)
  have hbj : L.packing.vertex t j = b := congrArg Prod.fst (Sum.inr.inj hj)
  have hak : L.packing.vertex u k = a := congrArg Prod.fst (Sum.inr.inj hk)
  have hbl : L.packing.vertex u l = b := congrArg Prod.fst (Sum.inr.inj hl)
  have hix : (triplingCrossVertex p i).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [threePointMatchingLeaveVertex] using hi))
  have hjy : (triplingCrossVertex p j).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [threePointMatchingLeaveVertex] using hj))
  have hkx : (triplingCrossVertex p' k).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [threePointMatchingLeaveVertex] using hk))
  have hly : (triplingCrossVertex p' l).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [threePointMatchingLeaveVertex] using hl))
  have htu : t = u := L.packing.pair_covered_at_most_once a b hab t u
    ⟨i, hai⟩ ⟨j, hbj⟩ ⟨k, hak⟩ ⟨l, hbl⟩
  subst u
  have hik : i = k := L.packing.vertex_injective t (hai.trans hak.symm)
  have hjl : j = l := L.packing.vertex_injective t (hbj.trans hbl.symm)
  subst k
  subst l
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = L.packing.vertex t i := hai.symm
      _ = L.packing.vertex t j := by rw [hij]
      _ = b := hbj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p₀, hp₀, hp₀uniq⟩
  have hp :
      (∃ h : Fin 3, triplingCrossVertex p h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hix
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hjy
  have hp' :
      (∃ h : Fin 3, triplingCrossVertex p' h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p' h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hkx
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hly
  have hpp : p = p' := (hp₀uniq p hp).trans (hp₀uniq p' hp').symm
  subst p'
  rfl

private theorem threePointMatchingLeavePacking_pair_covered_at_most_once
    (L : TrianglePacking.WithMatchingLeave α) :
    ∀ x y : ZMod 5 ⊕ (α × ZMod 3), x ≠ y →
      ∀ t u : ThreePointMatchingLeaveTriangleIndex L,
        (∃ i : Fin 3, threePointMatchingLeaveVertex L t i = x) →
        (∃ j : Fin 3, threePointMatchingLeaveVertex L t j = y) →
        (∃ i : Fin 3, threePointMatchingLeaveVertex L u i = x) →
        (∃ j : Fin 3, threePointMatchingLeaveVertex L u j = y) → t = u := by
  rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hxy t u htx hty hux huy
  · have hrs : r ≠ s := by
      intro hrs
      apply hxy
      rw [hrs]
    rcases threePointMatchingLeaveTriangle_eq_residual_of_covers_two_residual
      L r s hrs t htx hty with ⟨p, hp, hpr, hps⟩
    rcases threePointMatchingLeaveTriangle_eq_residual_of_covers_two_residual
      L r s hrs u hux huy with ⟨q, hq, hqr, hqs⟩
    calc
      t = Sum.inl p := hp
      _ = Sum.inl q := congrArg Sum.inl
        (fivePointResidualPacking.pair_covered_at_most_once r s hrs p q hpr hps hqr hqs)
      _ = u := hq.symm
  · rcases threePointMatchingLeaveTriangle_eq_block_of_covers_residual_group
      L r b y t htx hty with ⟨q, hq, hqr, hqy⟩
    rcases threePointMatchingLeaveTriangle_eq_block_of_covers_residual_group
      L r b y u hux huy with ⟨q', hq', hq'r, hq'y⟩
    rcases q with ⟨v, p⟩
    rcases q' with ⟨w, p'⟩
    have hqq' : (⟨v, p⟩ : ThreePointMatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
      threePointMatchingBlockTriangleIndex_eq_of_contains_right_pair L.matching b y (Sum.inl r)
        (by simp) v w p p' hqy hqr hq'y hq'r
    calc
      t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
      _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
      _ = u := hq'.symm
  · rcases threePointMatchingLeaveTriangle_eq_block_of_covers_residual_group
      L s a x t hty htx with ⟨q, hq, hqs, hqx⟩
    rcases threePointMatchingLeaveTriangle_eq_block_of_covers_residual_group
      L s a x u huy hux with ⟨q', hq', hq's, hq'x⟩
    rcases q with ⟨v, p⟩
    rcases q' with ⟨w, p'⟩
    have hqq' : (⟨v, p⟩ : ThreePointMatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
      threePointMatchingBlockTriangleIndex_eq_of_contains_right_pair L.matching a x (Sum.inl s)
        (by simp) v w p p' hqx hqs hq'x hq's
    calc
      t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
      _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
      _ = u := hq'.symm
  · by_cases hab : a = b
    · subst b
      have hxy' : x ≠ y := by
        intro hxy'
        apply hxy
        simp [hxy']
      rcases threePointMatchingLeaveTriangle_eq_block_of_covers_same_group_pair
        L a x y hxy' t htx hty with ⟨q, hq, hqx, hqy⟩
      rcases threePointMatchingLeaveTriangle_eq_block_of_covers_same_group_pair
        L a x y hxy' u hux huy with ⟨q', hq', hq'x, hq'y⟩
      rcases q with ⟨v, p⟩
      rcases q' with ⟨w, p'⟩
      have hqq' : (⟨v, p⟩ : ThreePointMatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
        threePointMatchingBlockTriangleIndex_eq_of_contains_right_pair L.matching a x
          (Sum.inr (a, y)) hxy v w p p' hqx hqy hq'x hq'y
      calc
        t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
        _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
        _ = u := hq'.symm
    · by_cases hmatching : L.matching.perm a = b
      · rcases threePointMatchingLeaveTriangle_eq_block_of_covers_matching_groups
          L a b x y hab hmatching t htx hty with ⟨q, hq, hqx, hqy⟩
        rcases threePointMatchingLeaveTriangle_eq_block_of_covers_matching_groups
          L a b x y hab hmatching u hux huy with ⟨q', hq', hq'x, hq'y⟩
        rcases q with ⟨v, p⟩
        rcases q' with ⟨w, p'⟩
        have hqq' : (⟨v, p⟩ : ThreePointMatchingBlockTriangleIndex L.matching) = ⟨w, p'⟩ :=
          threePointMatchingBlockTriangleIndex_eq_of_contains_right_pair L.matching a x
            (Sum.inr (b, y)) hxy v w p p' hqx hqy hq'x hq'y
        calc
          t = Sum.inr (Sum.inl ⟨v, p⟩) := hq
          _ = Sum.inr (Sum.inl ⟨w, p'⟩) := congrArg (fun z => Sum.inr (Sum.inl z)) hqq'
          _ = u := hq'.symm
      · rcases threePointMatchingLeaveTriangle_eq_transversal_of_covers_nonmatching_groups
          L a b x y hab hmatching t htx hty with ⟨q, hq, hqx, hqy⟩
        rcases threePointMatchingLeaveTriangle_eq_transversal_of_covers_nonmatching_groups
          L a b x y hab hmatching u hux huy with ⟨q', hq', hq'x, hq'y⟩
        have hqq' : q = q' :=
          threePointMatchingLeaveTransversalTriangleIndex_eq_of_distinct_groups L a b x y hab q q'
            hqx hqy hq'x hq'y
        calc
          t = Sum.inr (Sum.inr q) := hq
          _ = Sum.inr (Sum.inr q') := congrArg (fun z => Sum.inr (Sum.inr z)) hqq'
          _ = u := hq'.symm

/-- The three-point-group matching-leave expansion used by Feder--Subi's
`m ≡ 4 (mod 6)` case. -/
private noncomputable def threePointMatchingLeavePacking
    (L : TrianglePacking.WithMatchingLeave α) : TrianglePacking (ZMod 5 ⊕ (α × ZMod 3)) where
  Triangle := ThreePointMatchingLeaveTriangleIndex L
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := by classical exact Classical.decEq _
  vertex := threePointMatchingLeaveVertex L
  vertex_injective := threePointMatchingLeaveVertex_injective L
  pair_covered_at_most_once := threePointMatchingLeavePacking_pair_covered_at_most_once L

private noncomputable def threePointBlockCliqueIndex (M : EvenPairing α)
    (u : MatchingRepresentative M) (a : α) (x : ZMod 3) : ZMod 6 :=
  if a = u.1 then zModSixEquivFinTwoZModThree.symm (0, x)
  else zModSixEquivFinTwoZModThree.symm (1, x)

private theorem threePointBlockMap_cliqueIndex
    (M : EvenPairing α) (u : MatchingRepresentative M) (a : α) (x : ZMod 3)
    (ha : a = u.1 ∨ a = M.perm u.1) :
    threePointBlockMap M u (Sum.inr (threePointBlockCliqueIndex M u a x)) =
      Sum.inr (a, x) := by
  unfold threePointBlockCliqueIndex
  split
  · rename_i h
    simp [threePointBlockMap, h]
  · rename_i h
    rcases ha with ha | ha
    · exact False.elim (h ha)
    · simp [threePointBlockMap, h, ha]

private theorem threePointBlockPacking_covers_residual_group
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (r : ZMod 5) (a : α) (x : ZMod 3)
    (ha : a = u.1 ∨ a = M.perm u.1) :
    (threePointBlockPacking M u).CoversPair (Sum.inl r) (Sum.inr (a, x)) := by
  let z := threePointBlockCliqueIndex M u a x
  rcases sixPointSplitPacking_covers_residual_clique r z with ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  refine ⟨t, ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · exact (congrArg (threePointBlockMap M u) hi).trans rfl
  · exact (congrArg (threePointBlockMap M u) hj).trans
      (threePointBlockMap_cliqueIndex M u a x ha)

private theorem threePointBlockPacking_covers_clique_pair
    (M : EvenPairing α) (u : MatchingRepresentative M)
    (a b : α) (x y : ZMod 3)
    (ha : a = u.1 ∨ a = M.perm u.1)
    (hb : b = u.1 ∨ b = M.perm u.1)
    (hxy : (Sum.inr (a, x) : ZMod 5 ⊕ (α × ZMod 3)) ≠ Sum.inr (b, y)) :
    (threePointBlockPacking M u).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  let z := threePointBlockCliqueIndex M u a x
  let w := threePointBlockCliqueIndex M u b y
  have hzw : z ≠ w := by
    intro hzw
    apply hxy
    calc
      Sum.inr (a, x) = threePointBlockMap M u (Sum.inr z) :=
        (threePointBlockMap_cliqueIndex M u a x ha).symm
      _ = threePointBlockMap M u (Sum.inr w) := by rw [hzw]
      _ = Sum.inr (b, y) := threePointBlockMap_cliqueIndex M u b y hb
  rcases sixPointSplitPacking_covers_clique_pair z w hzw with ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  exact ⟨t,
    ⟨i, (congrArg (threePointBlockMap M u) hi).trans
      (threePointBlockMap_cliqueIndex M u a x ha)⟩,
    ⟨j, (congrArg (threePointBlockMap M u) hj).trans
      (threePointBlockMap_cliqueIndex M u b y hb)⟩⟩

private theorem threePointMatchingLeavePacking_covers_residual_pair_iff
    (L : TrianglePacking.WithMatchingLeave α) (r s : ZMod 5) (hrs : r ≠ s) :
    (threePointMatchingLeavePacking L).CoversPair (Sum.inl r) (Sum.inl s) ↔
      fivePointResidualPacking.CoversPair r s := by
  constructor
  · rintro ⟨t, hr, hs⟩
    rcases threePointMatchingLeaveTriangle_eq_residual_of_covers_two_residual L r s hrs t hr hs with
      ⟨p, hp, hpr, hps⟩
    exact ⟨p, hpr, hps⟩
  · rintro ⟨p, hr, hs⟩
    rcases hr with ⟨i, hi⟩
    rcases hs with ⟨j, hj⟩
    exact ⟨Sum.inl p, ⟨i, congrArg Sum.inl hi⟩, ⟨j, congrArg Sum.inl hj⟩⟩

private theorem threePointMatchingLeavePacking_covers_residual_group
    (L : TrianglePacking.WithMatchingLeave α) (r : ZMod 5) (a : α) (x : ZMod 3) :
    (threePointMatchingLeavePacking L).CoversPair (Sum.inl r) (Sum.inr (a, x)) := by
  let u := matchingRepresentative L.matching a
  have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
    matchingRepresentative_endpoints L.matching a
  rcases threePointBlockPacking_covers_residual_group L.matching u r a x ha with ⟨t, hr, hx⟩
  exact ⟨Sum.inr (Sum.inl ⟨u, t⟩), hr, hx⟩

private theorem threePointMatchingLeavePacking_covers_same_group_pair
    (L : TrianglePacking.WithMatchingLeave α) (a : α) (x y : ZMod 3) (hxy : x ≠ y) :
    (threePointMatchingLeavePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (a, y)) := by
  let u := matchingRepresentative L.matching a
  have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
    matchingRepresentative_endpoints L.matching a
  have hpair : (Sum.inr (a, x) : ZMod 5 ⊕ (α × ZMod 3)) ≠ Sum.inr (a, y) := by
    intro h
    apply hxy
    exact congrArg Prod.snd (Sum.inr.inj h)
  rcases threePointBlockPacking_covers_clique_pair L.matching u a a x y ha ha hpair with
    ⟨t, hx, hy⟩
  exact ⟨Sum.inr (Sum.inl ⟨u, t⟩), hx, hy⟩

private theorem threePointMatchingLeavePacking_covers_matching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hmatching : L.matching.perm a = b) :
    (threePointMatchingLeavePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  let u := matchingRepresentative L.matching a
  have ha : a = u.1 ∨ a = L.matching.perm u.1 :=
    matchingRepresentative_endpoints L.matching a
  have hb : b = u.1 ∨ b = L.matching.perm u.1 := by
    rcases ha with ha | ha
    · right
      calc
        b = L.matching.perm a := hmatching.symm
        _ = L.matching.perm u.1 := by rw [ha]
    · left
      calc
        b = L.matching.perm a := hmatching.symm
        _ = L.matching.perm (L.matching.perm u.1) := by rw [ha]
        _ = u.1 := L.matching.apply_apply _
  have hpair : (Sum.inr (a, x) : ZMod 5 ⊕ (α × ZMod 3)) ≠ Sum.inr (b, y) := by
    intro h
    apply hab
    exact congrArg Prod.fst (Sum.inr.inj h)
  rcases threePointBlockPacking_covers_clique_pair L.matching u a b x y ha hb hpair with
    ⟨t, hx, hy⟩
  exact ⟨Sum.inr (Sum.inl ⟨u, t⟩), hx, hy⟩

private theorem threePointMatchingLeavePacking_covers_nonmatching_groups
    (L : TrianglePacking.WithMatchingLeave α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hnonmatching : L.matching.perm a ≠ b) :
    (threePointMatchingLeavePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  rcases (L.coversPair_iff a b hab).mpr hnonmatching with ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = L.packing.vertex t i := hi.symm
      _ = L.packing.vertex t j := by rw [hij]
      _ = b := hj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p, hp, hpuniq⟩
  rcases hp with ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hki : k = i := triplingCrossVertex_index_eq_fst hk
  have hlj : l = j := triplingCrossVertex_index_eq_fst hl
  subst k
  subst l
  refine ⟨Sum.inr (Sum.inr (t, p)), ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · change Sum.inr (L.packing.vertex t i, (triplingCrossVertex p i).2) = Sum.inr (a, x)
    apply congrArg Sum.inr
    have hoffset : (triplingCrossVertex p i).2 = x := congrArg Prod.snd hk
    rw [hi, hoffset]
  · change Sum.inr (L.packing.vertex t j, (triplingCrossVertex p j).2) = Sum.inr (b, y)
    apply congrArg Sum.inr
    have hoffset : (triplingCrossVertex p j).2 = y := congrArg Prod.snd hl
    rw [hj, hoffset]

private def threePointLeaveVertex (i : Fin 4) : ZMod 5 ⊕ (α × ZMod 3) :=
  Sum.inl (fivePointResidualLeaveVertex i)

private theorem threePointLeave_cycle_iff (r s : ZMod 5) :
    (∃ i : Fin 4, s(Sum.inl r, Sum.inl s) =
      s(threePointLeaveVertex (α := α) i,
        threePointLeaveVertex (α := α) (fourCycleNext i))) ↔
      ∃ i : Fin 4, s(r, s) =
        s(fivePointResidualLeaveVertex i, fivePointResidualLeaveVertex (fourCycleNext i)) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Sym2.map.injective (fun x y h => Sum.inl.inj h)
    simpa only [Sym2.map_mk, threePointLeaveVertex] using hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa only [Sym2.map_mk, threePointLeaveVertex] using congrArg (Sym2.map Sum.inl) hi

/-- The three-point version of Feder--Subi's matching-leave expansion has the
same four-cycle leave in its common five-point residual side. -/
private theorem threePointMatchingLeavePacking_leavesFourCycle
    (L : TrianglePacking.WithMatchingLeave α) :
    (threePointMatchingLeavePacking L).LeavesFourCycle (threePointLeaveVertex (α := α)) := by
  constructor
  · intro i j hij
    apply fivePointResidualPacking_leavesFourCycle.1
    exact Sum.inl.inj hij
  · rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hxy
    · have hrs : r ≠ s := by
        intro hrs
        apply hxy
        rw [hrs]
      constructor
      · intro hcover
        have hbase : fivePointResidualPacking.CoversPair r s :=
          (threePointMatchingLeavePacking_covers_residual_pair_iff L r s hrs).mp hcover
        have hnotbase : ¬ ∃ i : Fin 4, s(r, s) =
            s(fivePointResidualLeaveVertex i, fivePointResidualLeaveVertex (fourCycleNext i)) :=
          (fivePointResidualPacking_leavesFourCycle.2 r s hrs).mp hbase
        intro hcycle
        apply hnotbase
        exact (threePointLeave_cycle_iff (α := α) r s).mp hcycle
      · intro hnotcycle
        apply (threePointMatchingLeavePacking_covers_residual_pair_iff L r s hrs).mpr
        apply (fivePointResidualPacking_leavesFourCycle.2 r s hrs).mpr
        intro hbasecycle
        apply hnotcycle
        exact (threePointLeave_cycle_iff (α := α) r s).mpr hbasecycle
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨_, hright⟩ | ⟨_, hright⟩
        · simp [threePointLeaveVertex] at hright
        · simp [threePointLeaveVertex] at hright
      · intro hnotcycle
        exact threePointMatchingLeavePacking_covers_residual_group L r b y
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [threePointLeaveVertex] at hleft
        · simp [threePointLeaveVertex] at hleft
      · intro hnotcycle
        rcases threePointMatchingLeavePacking_covers_residual_group L s a x with ⟨t, hs, ha⟩
        exact ⟨t, ha, hs⟩
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [threePointLeaveVertex] at hleft
        · simp [threePointLeaveVertex] at hleft
      · intro hnotcycle
        by_cases hab : a = b
        · subst b
          have hxy' : x ≠ y := by
            intro hxy'
            apply hxy
            simp [hxy']
          exact threePointMatchingLeavePacking_covers_same_group_pair L a x y hxy'
        · by_cases hmatching : L.matching.perm a = b
          · exact threePointMatchingLeavePacking_covers_matching_groups L a b x y hab hmatching
          · exact threePointMatchingLeavePacking_covers_nonmatching_groups L a b x y hab hmatching

private theorem card_threePointMatchingLeaveCarrier (m : ℕ) :
    Fintype.card (ZMod 5 ⊕ (Fin (2 * m) × ZMod 3)) = 6 * m + 5 := by
  norm_num [Fintype.card_sum, Fintype.card_prod, ZMod.card]
  omega

/-- Finite-label form of the source's three-point-group construction. -/
private noncomputable def threePointMatchingLeavePackingFin
    (S : SteinerTripleSystem (Fin (2 * m + 1))) : TrianglePacking (Fin (6 * m + 5)) := by
  let e : ZMod 5 ⊕ (Fin (2 * m) × ZMod 3) ≃ Fin (6 * m + 5) :=
    Fintype.equivFinOfCardEq (card_threePointMatchingLeaveCarrier m)
  exact (threePointMatchingLeavePacking (centerRemovedWithMatchingLeaveFin S)).map e

/-- Feder--Subi's `m ≡ 4 (mod 6)` source case.  The macro STS has order
`2m+1 ≡ 3 (mod 6)`; after center removal, matched pairs of three-point groups
are filled by the checked Walecki split block. -/
theorem exists_threePointMatchingLeavePackingFin_leavesFourCycle_of_modSix
    (m : ℕ) (hm : m % 6 = 4) :
    ∃ v : Fin 4 → Fin (6 * m + 5),
      (threePointMatchingLeavePackingFin (m := m)
        (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (2 * m + 1) (by
          right
          omega)).some).LeavesFourCycle v := by
  let S : SteinerTripleSystem (Fin (2 * m + 1)) :=
    (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (2 * m + 1) (by
      right
      omega)).some
  let e : ZMod 5 ⊕ (Fin (2 * m) × ZMod 3) ≃ Fin (6 * m + 5) :=
    Fintype.equivFinOfCardEq (card_threePointMatchingLeaveCarrier m)
  refine ⟨e ∘ threePointLeaveVertex, ?_⟩
  exact TrianglePacking.map_leavesFourCycle e
    (threePointMatchingLeavePacking (centerRemovedWithMatchingLeaveFin S)) threePointLeaveVertex
    (threePointMatchingLeavePacking_leavesFourCycle (centerRemovedWithMatchingLeaveFin S))

end ThreePointMacroExpansion

section ThreeMatchingLeaveMacro

open AppliedModelingLib.Foundations.Graph

/-- The first two leaves of a three-matching macro packing form the even
cycles that Feder--Subi orient in their final residue class. -/
private noncomputable def threeLeaveAlternatingPairing
    (L : TrianglePacking.WithThreeMatchingLeaves α) : AlternatingPairing α where
  first := L.matching 0
  second := L.matching 1
  distinct := by
    intro a h
    exact L.matching_edges_disjoint 0 1 (by decide) a h

/-- The directed neighbour whose three-point fibre supplies the three
Feder--Subi cycle triangles. -/
private noncomputable def threeLeaveOrientedPartner
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) : α :=
  (threeLeaveAlternatingPairing L).orientedPartner a

private theorem threeLeaveOrientedPartner_ne
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) :
    threeLeaveOrientedPartner L a ≠ a :=
  (threeLeaveAlternatingPairing L).orientedPartner_ne a

private theorem threeLeaveOrientedPartner_not_reverse
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) :
    threeLeaveOrientedPartner L (threeLeaveOrientedPartner L a) ≠ a :=
  (threeLeaveAlternatingPairing L).orientedPartner_not_reverse a

private theorem threeLeaveOrientedPartner_matches
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) :
    threeLeaveOrientedPartner L a = (L.matching 0).perm a ∨
      threeLeaveOrientedPartner L a = (L.matching 1).perm a := by
  unfold threeLeaveOrientedPartner AppliedModelingLib.Foundations.Graph.AlternatingPairing.orientedPartner
  split <;> simp [threeLeaveAlternatingPairing]

private theorem threeLeave_first_edge_oriented
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) :
    threeLeaveOrientedPartner L a = (L.matching 0).perm a ∨
      threeLeaveOrientedPartner L ((L.matching 0).perm a) = a :=
  (threeLeaveAlternatingPairing L).first_edge_oriented a

private theorem threeLeave_second_edge_oriented
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) :
    threeLeaveOrientedPartner L a = (L.matching 1).perm a ∨
      threeLeaveOrientedPartner L ((L.matching 1).perm a) = a :=
  (threeLeaveAlternatingPairing L).second_edge_oriented a

private theorem zModThree_add_two_ne (q : ZMod 3) : q ≠ q + 2 := by
  intro h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_add] at hval
  norm_num [ZMod.val_two_eq_two_mod] at hval
  have hlt := ZMod.val_lt q
  omega

private theorem zModThree_add_two_ne_rev (q : ZMod 3) : q + 2 ≠ q :=
  (zModThree_add_two_ne q).symm

private theorem zModThree_add_one_ne (q : ZMod 3) : q ≠ q + 1 := by
  intro h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_add] at hval
  norm_num [ZMod.val_one_eq_one_mod] at hval
  have hlt := ZMod.val_lt q
  omega

private theorem zModThree_eq_self_or_add_one_or_add_two (x y : ZMod 3) :
    y = x ∨ y = x + 1 ∨ y = x + 2 := by
  have hlt := (y - x).val_lt
  interval_cases hval : (y - x).val
  · left
    have hzero : y - x = 0 := by
      apply ZMod.val_injective 3
      simpa [hval]
    calc
      y = x + (y - x) := by ring
      _ = x := by rw [hzero, add_zero]
  · right
    left
    have hone : y - x = 1 := by
      apply ZMod.val_injective 3
      simpa [hval, ZMod.val_one_eq_one_mod]
    calc
      y = x + (y - x) := by ring
      _ = x + 1 := by rw [hone]
  · right
    right
    have htwo : y - x = 2 := by
      apply ZMod.val_injective 3
      simpa [hval, ZMod.val_two_eq_two_mod]
    calc
      y = x + (y - x) := by ring
      _ = x + 2 := by rw [htwo]

/-- The macro packing's transversal triangles, together with the three
triangles that consume one fibre's internal `K₃` along every directed
first/second-leave edge. -/
private abbrev ThreeMatchingLeaveMacroTriangleIndex
    (L : TrianglePacking.WithThreeMatchingLeaves α) :=
  (L.packing.Triangle × (ZMod 3 × ZMod 3)) ⊕ (α × ZMod 3)

private noncomputable def threeMatchingLeaveMacroVertex
    (L : TrianglePacking.WithThreeMatchingLeaves α) :
    ThreeMatchingLeaveMacroTriangleIndex L → Fin 3 → α × ZMod 3
  | Sum.inl ⟨t, p⟩ => fun i =>
      (L.packing.vertex t i, (triplingCrossVertex p i).2)
  | Sum.inr ⟨a, q⟩ => fun i =>
      if i = 0 then (a, q)
      else if i = 1 then (threeLeaveOrientedPartner L a, q + 1)
      else (a, q + 2)

private theorem threeMatchingLeaveMacroVertex_injective
    (L : TrianglePacking.WithThreeMatchingLeaves α)
    (t : ThreeMatchingLeaveMacroTriangleIndex L) :
    Function.Injective (threeMatchingLeaveMacroVertex L t) := by
  cases t with
  | inl q =>
      rcases q with ⟨t, p⟩
      intro i j hij
      apply L.packing.vertex_injective t
      exact congrArg Prod.fst hij
  | inr q =>
      rcases q with ⟨a, q⟩
      intro i j hij
      fin_cases i
      · fin_cases j
        · rfl
        · exact False.elim (threeLeaveOrientedPartner_ne L a
            (congrArg Prod.fst hij).symm)
        · exact False.elim (zModThree_add_two_ne q (congrArg Prod.snd hij))
      · fin_cases j
        · exact False.elim (threeLeaveOrientedPartner_ne L a
            (congrArg Prod.fst hij))
        · rfl
        · exact False.elim (threeLeaveOrientedPartner_ne L a
            (congrArg Prod.fst hij))
      · fin_cases j
        · exact False.elim (zModThree_add_two_ne_rev q (congrArg Prod.snd hij))
        · exact False.elim (threeLeaveOrientedPartner_ne L a
            (congrArg Prod.fst hij).symm)
        · rfl

/-- The three residual vertices used for the three fibre matchings above a
third matching edge. -/
private def mFiveThirdResidual (r : Fin 3) : Fin 5 :=
  ⟨r.1, by omega⟩

/-- The remaining two residual vertices, assigned to the first and second
macro matching respectively. -/
private def mFiveFirstSecondResidual (k : Fin 2) : Fin 5 :=
  ⟨k.1 + 3, by omega⟩

private def mFiveFirstSecondMatching (k : Fin 2) : Fin 3 :=
  Fin.castAdd 1 k

private theorem mFiveFirstSecond_edge_oriented
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a b : α)
    (hmatching : (L.matching (mFiveFirstSecondMatching k)).perm a = b) :
    threeLeaveOrientedPartner L a = b ∨ threeLeaveOrientedPartner L b = a := by
  fin_cases k
  · have hmatch : (L.matching 0).perm a = b := by
      simpa [mFiveFirstSecondMatching] using hmatching
    rcases threeLeave_first_edge_oriented L a with h | h
    · exact Or.inl (h.trans hmatch)
    · exact Or.inr (by simpa [hmatch] using h)
  · have hmatch : (L.matching 1).perm a = b := by
      simpa [mFiveFirstSecondMatching] using hmatching
    rcases threeLeave_second_edge_oriented L a with h | h
    · exact Or.inl (h.trans hmatch)
    · exact Or.inr (by simpa [hmatch] using h)

/-- Literal triangle indices for Feder--Subi's final `m ≡ 5` residue case.
The first summand is the residual `K₅`; the next two attach its five vertices
to the three macro matching leaves; the final two are the macro transversals
and the oriented alternating-cycle triangles. -/
private abbrev MFiveTriangleIndex (L : TrianglePacking.WithThreeMatchingLeaves α) :=
  Bool ⊕ ((Σ r : Fin 3, MatchingRepresentative (L.matching 2) × ZMod 3) ⊕
    ((Σ k : Fin 2, MatchingRepresentative (L.matching (mFiveFirstSecondMatching k)) × ZMod 3) ⊕
      ((L.packing.Triangle × (ZMod 3 × ZMod 3)) ⊕ (α × ZMod 3))))

private noncomputable def mFiveVertex (L : TrianglePacking.WithThreeMatchingLeaves α) :
    MFiveTriangleIndex L → Fin 3 → Fin 5 ⊕ (α × ZMod 3)
  | Sum.inl p => fun i => Sum.inl (finFive.vertex p i)
  | Sum.inr (Sum.inl ⟨r, ⟨u, x⟩⟩) => fun i =>
      if i = 0 then Sum.inl (mFiveThirdResidual r)
      else if i = 1 then Sum.inr (u.1, x)
      else Sum.inr ((L.matching 2).perm u.1, x + (r.1 : ZMod 3))
  | Sum.inr (Sum.inr (Sum.inl ⟨k, ⟨u, x⟩⟩)) => fun i =>
      if i = 0 then Sum.inl (mFiveFirstSecondResidual k)
      else if i = 1 then Sum.inr (u.1, x)
      else Sum.inr ((L.matching (mFiveFirstSecondMatching k)).perm u.1, x)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨t, p⟩))) => fun i =>
      Sum.inr (L.packing.vertex t i, (triplingCrossVertex p i).2)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨a, q⟩))) => fun i =>
      Sum.inr (threeMatchingLeaveMacroVertex L (Sum.inr (a, q)) i)

private theorem mFiveVertex_injective
    (L : TrianglePacking.WithThreeMatchingLeaves α) (t : MFiveTriangleIndex L) :
    Function.Injective (mFiveVertex L t) := by
  cases t with
  | inl p =>
      intro i j hij
      apply finFive.vertex_injective p
      exact Sum.inl.inj hij
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨r, u, x⟩
          intro i j hij
          fin_cases i
          · fin_cases j
            · rfl
            · simp [mFiveVertex] at hij
            · simp [mFiveVertex] at hij
          · fin_cases j
            · simp [mFiveVertex] at hij
            · rfl
            · have hpartner : u.1 = (L.matching 2).perm u.1 := by
                have hfirst := congrArg (Sum.elim (fun _ : Fin 5 => u.1) Prod.fst) hij
                simpa [mFiveVertex] using hfirst
              exact False.elim ((L.matching 2).apply_ne u.1 hpartner.symm)
          · fin_cases j
            · simp [mFiveVertex] at hij
            · have hpartner : (L.matching 2).perm u.1 = u.1 := by
                have hfirst := congrArg (Sum.elim (fun _ : Fin 5 => u.1) Prod.fst) hij
                simpa [mFiveVertex] using hfirst
              exact False.elim ((L.matching 2).apply_ne u.1 hpartner)
            · rfl
      | inr q =>
          cases q with
          | inl q =>
              rcases q with ⟨k, u, x⟩
              intro i j hij
              fin_cases i
              · fin_cases j
                · rfl
                · simp [mFiveVertex] at hij
                · simp [mFiveVertex] at hij
              · fin_cases j
                · simp [mFiveVertex] at hij
                · rfl
                · have hpartner : u.1 =
                      (L.matching (mFiveFirstSecondMatching k)).perm u.1 := by
                    have hfirst := congrArg (Sum.elim (fun _ : Fin 5 => u.1) Prod.fst) hij
                    simpa [mFiveVertex] using hfirst
                  exact False.elim
                    ((L.matching (mFiveFirstSecondMatching k)).apply_ne u.1 hpartner.symm)
              · fin_cases j
                · simp [mFiveVertex] at hij
                · have hpartner : (L.matching (mFiveFirstSecondMatching k)).perm u.1 = u.1 := by
                    have hfirst := congrArg (Sum.elim (fun _ : Fin 5 => u.1) Prod.fst) hij
                    simpa [mFiveVertex] using hfirst
                  exact False.elim
                    ((L.matching (mFiveFirstSecondMatching k)).apply_ne u.1 hpartner)
                · rfl
          | inr q =>
              cases q with
              | inl q =>
                  rcases q with ⟨t, p⟩
                  intro i j hij
                  apply L.packing.vertex_injective t
                  exact congrArg Prod.fst (Sum.inr.inj hij)
              | inr q =>
                  rcases q with ⟨a, x⟩
                  intro i j hij
                  apply threeMatchingLeaveMacroVertex_injective L (Sum.inr (a, x))
                  exact Sum.inr.inj hij

private theorem mFiveTriangle_eq_residual_of_covers_two_residual
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r s : Fin 5) (hrs : r ≠ s)
    (t : MFiveTriangleIndex L)
    (hr : ∃ i : Fin 3, mFiveVertex L t i = Sum.inl r)
    (hs : ∃ j : Fin 3, mFiveVertex L t j = Sum.inl s) :
    ∃ p : Bool, t = Sum.inl p ∧
      (∃ i : Fin 3, finFive.vertex p i = r) ∧
        ∃ j : Fin 3, finFive.vertex p j = s := by
  rcases hr with ⟨i, hi⟩
  rcases hs with ⟨j, hj⟩
  cases t with
  | inl p => exact ⟨p, rfl, ⟨i, Sum.inl.inj hi⟩, ⟨j, Sum.inl.inj hj⟩⟩
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨u, v, x⟩
          fin_cases i <;> fin_cases j <;> simp [mFiveVertex] at hi hj
          exact False.elim (hrs (hi.symm.trans hj))
      | inr q =>
          cases q with
          | inl q =>
              rcases q with ⟨u, v, x⟩
              fin_cases i <;> fin_cases j <;> simp [mFiveVertex] at hi hj
              exact False.elim (hrs (hi.symm.trans hj))
          | inr q =>
              cases q with
              | inl q =>
                  rcases q with ⟨u, v⟩
                  fin_cases i <;> simp [mFiveVertex] at hi
              | inr q =>
                  rcases q with ⟨u, v⟩
                  fin_cases i <;> simp [mFiveVertex] at hi

private theorem mFiveTriangle_eq_matching_of_covers_residual_group
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 5) (a : α) (x : ZMod 3)
    (t : MFiveTriangleIndex L)
    (hr : ∃ i : Fin 3, mFiveVertex L t i = Sum.inl r)
    (hx : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (a, x)) :
    (∃ q : Σ u : Fin 3, MatchingRepresentative (L.matching 2) × ZMod 3,
      t = Sum.inr (Sum.inl q) ∧
        (∃ i : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) i = Sum.inl r) ∧
          ∃ j : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (a, x)) ∨
      ∃ q : Σ u : Fin 2,
        MatchingRepresentative (L.matching (mFiveFirstSecondMatching u)) × ZMod 3,
        t = Sum.inr (Sum.inr (Sum.inl q)) ∧
          (∃ i : Fin 3, mFiveVertex L (Sum.inr (Sum.inr (Sum.inl q))) i = Sum.inl r) ∧
            ∃ j : Fin 3,
              mFiveVertex L (Sum.inr (Sum.inr (Sum.inl q))) j = Sum.inr (a, x) := by
  rcases hr with ⟨i, hi⟩
  rcases hx with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases j <;> simp [mFiveVertex] at hj
  | inr q =>
      cases q with
      | inl q => exact Or.inl ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          cases q with
          | inl q => exact Or.inr ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
          | inr q =>
              cases q with
              | inl q => fin_cases i <;> simp [mFiveVertex] at hi
              | inr q => fin_cases i <;> simp [mFiveVertex] at hi

/-- The unique third-leave matching triangle through a prescribed residual
vertex and a prescribed point in a three-point fibre. -/
private noncomputable def mFiveThirdFactorTriangle
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 3) (a : α) (x : ZMod 3) :
    MFiveTriangleIndex L :=
  let u := matchingRepresentative (L.matching 2) a
  Sum.inr (Sum.inl ⟨r, u, if a = u.1 then x else x - (r.1 : ZMod 3)⟩)

private theorem mFiveThirdFactorTriangle_residual_vertex
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 3) (a : α) (x : ZMod 3) :
    mFiveVertex L (mFiveThirdFactorTriangle L r a x) 0 =
      Sum.inl (mFiveThirdResidual r) := by
  simp [mFiveThirdFactorTriangle, mFiveVertex]

private theorem mFiveThirdFactorTriangle_group_vertex
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 3) (a : α) (x : ZMod 3) :
    ∃ i : Fin 3,
      mFiveVertex L (mFiveThirdFactorTriangle L r a x) i = Sum.inr (a, x) := by
  let M := L.matching 2
  let u := matchingRepresentative M a
  rcases matchingRepresentative_endpoints M a with ha | ha
  · refine ⟨1, ?_⟩
    have hsame : (matchingRepresentative (L.matching 2) a).1 = a := by
      simpa [M] using ha.symm
    change Sum.inr ((matchingRepresentative (L.matching 2) a).1,
      if a = (matchingRepresentative (L.matching 2) a).1 then x
      else x - (r.1 : ZMod 3)) = Sum.inr (a, x)
    simp [hsame]
  · refine ⟨2, ?_⟩
    have hsame : (L.matching 2).perm (matchingRepresentative (L.matching 2) a).1 = a := by
      simpa [M] using ha.symm
    have hne : a ≠ (matchingRepresentative (L.matching 2) a).1 := by
      intro h
      apply (L.matching 2).apply_ne (matchingRepresentative (L.matching 2) a).1
      calc
        (L.matching 2).perm (matchingRepresentative (L.matching 2) a).1 = a := hsame
        _ = (matchingRepresentative (L.matching 2) a).1 := h
    change Sum.inr ((L.matching 2).perm (matchingRepresentative (L.matching 2) a).1,
      (if a = (matchingRepresentative (L.matching 2) a).1 then x
        else x - (r.1 : ZMod 3)) + (r.1 : ZMod 3)) = Sum.inr (a, x)
    rw [if_neg hne, hsame]
    congr 2
    ring

/-- A third-leave matching triangle containing its displayed residual and
fibre point is the canonical triangle selected by that pair. -/
private theorem mFiveThirdFactorTriangleIndex_eq_of_residual_group
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 3) (a : α) (x : ZMod 3)
    (q : Σ r : Fin 3, MatchingRepresentative (L.matching 2) × ZMod 3)
    (hr : ∃ i : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) i =
      Sum.inl (mFiveThirdResidual r))
    (hx : ∃ j : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (a, x)) :
    Sum.inr (Sum.inl q) = mFiveThirdFactorTriangle L r a x := by
  rcases q with ⟨r', u, z⟩
  rcases hr with ⟨i, hi⟩
  have hr' : r' = r := by
    fin_cases i
    · have hsum :
          (Sum.inl (mFiveThirdResidual r') : Fin 5 ⊕ (α × ZMod 3)) =
            Sum.inl (mFiveThirdResidual r) := by
          simpa [mFiveVertex] using hi
      have hres : mFiveThirdResidual r' = mFiveThirdResidual r := Sum.inl.inj hsum
      apply Fin.ext
      simpa [mFiveThirdResidual] using congrArg Fin.val hres
    · simp [mFiveVertex] at hi
    · simp [mFiveVertex] at hi
  subst r'
  rcases hx with ⟨j, hj⟩
  fin_cases j
  · simp [mFiveVertex] at hj
  · have hsum : (Sum.inr (u.1, z) : Fin 5 ⊕ (α × ZMod 3)) = Sum.inr (a, x) := by
      simpa [mFiveVertex] using hj
    have hpair : (u.1, z) = (a, x) := Sum.inr.inj hsum
    have hu : u.1 = a := congrArg Prod.fst hpair
    have hz : z = x := congrArg Prod.snd hpair
    have hrep : matchingRepresentative (L.matching 2) a = u :=
      matchingRepresentative_eq_of_endpoint _ u a (Or.inl hu.symm)
    subst u
    simp [mFiveThirdFactorTriangle, hu, hz]
  · have hsum :
        (Sum.inr ((L.matching 2).perm u.1, z + (r.1 : ZMod 3)) :
          Fin 5 ⊕ (α × ZMod 3)) = Sum.inr (a, x) := by
        simpa [mFiveVertex] using hj
    have hpair : ((L.matching 2).perm u.1, z + (r.1 : ZMod 3)) = (a, x) :=
      Sum.inr.inj hsum
    have hu : (L.matching 2).perm u.1 = a := congrArg Prod.fst hpair
    have hz : z + (r.1 : ZMod 3) = x := congrArg Prod.snd hpair
    have hrep : matchingRepresentative (L.matching 2) a = u :=
      matchingRepresentative_eq_of_endpoint _ u a (Or.inr hu.symm)
    have hne : a ≠ u.1 := by
      intro h
      apply (L.matching 2).apply_ne u.1
      calc
        (L.matching 2).perm u.1 = a := hu
        _ = u.1 := h
    subst u
    simp [mFiveThirdFactorTriangle, hne]
    congr 3
    calc
      z = (z + (r.1 : ZMod 3)) - (r.1 : ZMod 3) := by ring
      _ = x - (r.1 : ZMod 3) := by rw [hz]

/-- The unique first- or second-leave matching triangle through its assigned
residual vertex and a prescribed fibre point. -/
private noncomputable def mFiveFirstSecondFactorTriangle
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a : α) (x : ZMod 3) :
    MFiveTriangleIndex L :=
  Sum.inr (Sum.inr (Sum.inl ⟨k,
    matchingRepresentative (L.matching (mFiveFirstSecondMatching k)) a, x⟩))

private theorem mFiveFirstSecondFactorTriangle_residual_vertex
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a : α) (x : ZMod 3) :
    mFiveVertex L (mFiveFirstSecondFactorTriangle L k a x) 0 =
      Sum.inl (mFiveFirstSecondResidual k) := by
  simp [mFiveFirstSecondFactorTriangle, mFiveVertex]

private theorem mFiveFirstSecondFactorTriangle_group_vertex
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a : α) (x : ZMod 3) :
    ∃ i : Fin 3,
      mFiveVertex L (mFiveFirstSecondFactorTriangle L k a x) i = Sum.inr (a, x) := by
  let M := L.matching (mFiveFirstSecondMatching k)
  rcases matchingRepresentative_endpoints M a with ha | ha
  · refine ⟨1, ?_⟩
    have hsame : (matchingRepresentative (L.matching (mFiveFirstSecondMatching k)) a).1 = a := by
      simpa [M] using ha.symm
    simp [mFiveFirstSecondFactorTriangle, mFiveVertex, hsame]
  · refine ⟨2, ?_⟩
    have hsame : (L.matching (mFiveFirstSecondMatching k)).perm
        (matchingRepresentative (L.matching (mFiveFirstSecondMatching k)) a).1 = a := by
      simpa [M] using ha.symm
    simp [mFiveFirstSecondFactorTriangle, mFiveVertex, hsame]

private theorem mFiveFirstSecondFactorTriangleIndex_eq_of_residual_group
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a : α) (x : ZMod 3)
    (q : Σ k : Fin 2,
      MatchingRepresentative (L.matching (mFiveFirstSecondMatching k)) × ZMod 3)
    (hr : ∃ i : Fin 3, mFiveVertex L (Sum.inr (Sum.inr (Sum.inl q))) i =
      Sum.inl (mFiveFirstSecondResidual k))
    (hx : ∃ j : Fin 3, mFiveVertex L (Sum.inr (Sum.inr (Sum.inl q))) j =
      Sum.inr (a, x)) :
    Sum.inr (Sum.inr (Sum.inl q)) = mFiveFirstSecondFactorTriangle L k a x := by
  rcases q with ⟨k', u, z⟩
  rcases hr with ⟨i, hi⟩
  have hk' : k' = k := by
    fin_cases i
    · have hsum :
          (Sum.inl (mFiveFirstSecondResidual k') : Fin 5 ⊕ (α × ZMod 3)) =
            Sum.inl (mFiveFirstSecondResidual k) := by
          simpa [mFiveVertex] using hi
      have hres : mFiveFirstSecondResidual k' = mFiveFirstSecondResidual k := Sum.inl.inj hsum
      apply Fin.ext
      simpa [mFiveFirstSecondResidual] using congrArg Fin.val hres
    · simp [mFiveVertex] at hi
    · simp [mFiveVertex] at hi
  subst k'
  rcases hx with ⟨j, hj⟩
  fin_cases j
  · simp [mFiveVertex] at hj
  · have hsum : (Sum.inr (u.1, z) : Fin 5 ⊕ (α × ZMod 3)) = Sum.inr (a, x) := by
      simpa [mFiveVertex] using hj
    have hpair : (u.1, z) = (a, x) := Sum.inr.inj hsum
    have hu : u.1 = a := congrArg Prod.fst hpair
    have hz : z = x := congrArg Prod.snd hpair
    have hrep : matchingRepresentative (L.matching (mFiveFirstSecondMatching k)) a = u :=
      matchingRepresentative_eq_of_endpoint _ u a (Or.inl hu.symm)
    subst u
    simp [mFiveFirstSecondFactorTriangle, hz]
  · have hsum :
        (Sum.inr ((L.matching (mFiveFirstSecondMatching k)).perm u.1, z) :
          Fin 5 ⊕ (α × ZMod 3)) = Sum.inr (a, x) := by
        simpa [mFiveVertex] using hj
    have hpair : ((L.matching (mFiveFirstSecondMatching k)).perm u.1, z) = (a, x) :=
      Sum.inr.inj hsum
    have hu : (L.matching (mFiveFirstSecondMatching k)).perm u.1 = a :=
      congrArg Prod.fst hpair
    have hz : z = x := congrArg Prod.snd hpair
    have hrep : matchingRepresentative (L.matching (mFiveFirstSecondMatching k)) a = u :=
      matchingRepresentative_eq_of_endpoint _ u a (Or.inr hu.symm)
    subst u
    simp [mFiveFirstSecondFactorTriangle, hz]

private theorem mFiveTriangle_eq_fill_of_covers_same_group_pair
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) (x y : ZMod 3) (hxy : x ≠ y)
    (t : MFiveTriangleIndex L)
    (hx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (a, y)) :
    ∃ q : α × ZMod 3, t = Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) ∧
      (∃ i : Fin 3,
        mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) i = Sum.inr (a, x)) ∧
        ∃ j : Fin 3,
          mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) j = Sum.inr (a, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases i <;> simp [mFiveVertex] at hi
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨r, u, z⟩
          fin_cases i
          · simp [mFiveVertex] at hi
          · fin_cases j
            · simp [mFiveVertex] at hj
            · simp [mFiveVertex] at hi hj
              exact False.elim (hxy (hi.2.symm.trans hj.2))
            · simp [mFiveVertex] at hi hj
              exact False.elim ((L.matching 2).apply_ne u.1 (hj.1.trans hi.1.symm))
          · fin_cases j
            · simp [mFiveVertex] at hj
            · simp [mFiveVertex] at hi hj
              exact False.elim ((L.matching 2).apply_ne u.1 (hi.1.trans hj.1.symm))
            · simp [mFiveVertex] at hi hj
              exact False.elim (hxy (hi.2.symm.trans hj.2))
      | inr q =>
          cases q with
          | inl q =>
              rcases q with ⟨k, u, z⟩
              let M := L.matching (mFiveFirstSecondMatching k)
              fin_cases i
              · simp [mFiveVertex] at hi
              · fin_cases j
                · simp [mFiveVertex] at hj
                · simp [mFiveVertex] at hi hj
                  exact False.elim (hxy (hi.2.symm.trans hj.2))
                · simp [mFiveVertex] at hi hj
                  exact False.elim (M.apply_ne u.1 (hj.1.trans hi.1.symm))
              · fin_cases j
                · simp [mFiveVertex] at hj
                · simp [mFiveVertex] at hi hj
                  exact False.elim (M.apply_ne u.1 (hi.1.trans hj.1.symm))
                · simp [mFiveVertex] at hi hj
                  exact False.elim (hxy (hi.2.symm.trans hj.2))
          | inr q =>
              cases q with
              | inl q =>
                  rcases q with ⟨u, z⟩
                  have haui : L.packing.vertex u i = a :=
                    congrArg Prod.fst (Sum.inr.inj hi)
                  have hauj : L.packing.vertex u j = a :=
                    congrArg Prod.fst (Sum.inr.inj hj)
                  have hij : i = j := L.packing.vertex_injective u (haui.trans hauj.symm)
                  apply False.elim
                  apply hxy
                  calc
                    x = (triplingCrossVertex z i).2 :=
                      (congrArg Prod.snd (Sum.inr.inj hi)).symm
                    _ = (triplingCrossVertex z j).2 := by rw [hij]
                    _ = y := congrArg Prod.snd (Sum.inr.inj hj)
              | inr q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩

/-- The oriented fill triangle through two distinct points of the same fibre.
Exactly one of the two points is the repeated fibre vertex in the displayed
source triangle, and this orientation determines its index. -/
private noncomputable def mFiveFillTriangle
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) (x y : ZMod 3) :
    MFiveTriangleIndex L :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨a, if y = x + 2 then x else y⟩)))

/-- The oriented fill triangle through a first- or second-leave edge.  Its
source fibre is selected by the alternating-cycle orientation. -/
private noncomputable def mFiveFirstSecondFillTriangle
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3) :
    MFiveTriangleIndex L :=
  if threeLeaveOrientedPartner L a = b then
    Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨a, if y = x + 1 then x else y - 1⟩)))
  else
    Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨b, if y = x + 2 then y else x - 1⟩)))

/-- The first/second-leave oriented fill triangle is uniquely determined by
the two endpoints and their fibre labels. -/
private theorem mFiveFirstSecondFillTriangleIndex_eq_of_matched_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a b : α)
    (x y : ZMod 3) (hab : a ≠ b)
    (hmatching : (L.matching (mFiveFirstSecondMatching k)).perm a = b)
    (q : α × ZMod 3)
    (hx : ∃ i : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) j = Sum.inr (b, y)) :
    Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) =
      mFiveFirstSecondFillTriangle L a b x y := by
  classical
  rcases q with ⟨u, z⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  have sumInr_inj {p q : α × ZMod 3}
      (h : (Sum.inr p : Fin 5 ⊕ (α × ZMod 3)) = Sum.inr q) : p = q :=
    Sum.inr.inj h
  by_cases hor : threeLeaveOrientedPartner L a = b
  · have hreverse : threeLeaveOrientedPartner L b ≠ a := by
      intro hba
      apply threeLeaveOrientedPartner_not_reverse L a
      rw [hor, hba]
    fin_cases i
    · fin_cases j
      · have hix : (u, z) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
      · have hix : (u, z) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        have hu : u = a := congrArg Prod.fst hix
        have hz : z = x := congrArg Prod.snd hix
        have hrel : y = x + 1 := by
          calc
            y = z + 1 := (congrArg Prod.snd hjy).symm
            _ = x + 1 := by rw [hz]
        subst u
        subst z
        simp [mFiveFirstSecondFillTriangle, hor, hrel]
      · have hix : (u, z) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z + 2) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
    · fin_cases j
      · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        apply False.elim
        apply hreverse
        have hu : u = b := congrArg Prod.fst hjy
        calc
          threeLeaveOrientedPartner L b = threeLeaveOrientedPartner L u := by
            rw [hu]
          _ = a := congrArg Prod.fst hix
      · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
      · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z + 2) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        apply False.elim
        apply hreverse
        have hu : u = b := congrArg Prod.fst hjy
        calc
          threeLeaveOrientedPartner L b = threeLeaveOrientedPartner L u := by
            rw [hu]
          _ = a := congrArg Prod.fst hix
    · fin_cases j
      · have hix : (u, z + 2) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
      · have hix : (u, z + 2) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        have hu : u = a := congrArg Prod.fst hix
        have hzx : z + 2 = x := congrArg Prod.snd hix
        have hzy : z + 1 = y := congrArg Prod.snd hjy
        have hrel : y = x + 2 := by
          calc
            y = z + 1 := hzy.symm
            _ = (z + 2) + 2 := by
              rw [add_assoc, show (2 + 2 : ZMod 3) = 1 by decide]
            _ = x + 2 := by rw [hzx]
        have hnot : y ≠ x + 1 := by
          intro h
          have heq : x + 2 = x + 1 := hrel.symm.trans h
          apply zModThree_add_one_ne x
          calc
            x = (x + 1) + 2 := by
              rw [add_assoc, show (1 + 2 : ZMod 3) = 0 by decide, add_zero]
            _ = (x + 2) + 2 := by rw [heq.symm]
            _ = x + 1 := by
              rw [add_assoc, show (2 + 2 : ZMod 3) = 1 by decide]
        have hz : z = y - 1 := by
          calc
            z = (z + 1) - 1 := by ring
            _ = y - 1 := by rw [hzy]
        subst u
        subst z
        simp [mFiveFirstSecondFillTriangle, hor, hnot]
      · have hix : (u, z + 2) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z + 2) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
  · have hor' : threeLeaveOrientedPartner L b = a :=
      (mFiveFirstSecond_edge_oriented L k a b hmatching).resolve_left hor
    fin_cases i
    · fin_cases j
      · have hix : (u, z) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
      · have hix : (u, z) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        apply False.elim
        apply hor
        have hu : u = a := congrArg Prod.fst hix
        calc
          threeLeaveOrientedPartner L a = threeLeaveOrientedPartner L u := by
            rw [hu]
          _ = b := congrArg Prod.fst hjy
      · have hix : (u, z) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z + 2) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
    · fin_cases j
      · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        have hu : u = b := congrArg Prod.fst hjy
        have hz : z = y := congrArg Prod.snd hjy
        have hzx : z + 1 = x := congrArg Prod.snd hix
        have hrel : y = x + 2 := by
          calc
            y = z := hz.symm
            _ = (z + 1) + 2 := by
              rw [add_assoc, show (1 + 2 : ZMod 3) = 0 by decide, add_zero]
            _ = x + 2 := by rw [hzx]
        subst u
        subst z
        simp [mFiveFirstSecondFillTriangle, hor, hrel]
      · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
      · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z + 2) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        have hu : u = b := congrArg Prod.fst hjy
        have hzx : z + 1 = x := congrArg Prod.snd hix
        have hzy : z + 2 = y := congrArg Prod.snd hjy
        have hrel : y = x + 1 := by
          calc
            y = z + 2 := hzy.symm
            _ = (z + 1) + 1 := by ring
            _ = x + 1 := by rw [hzx]
        have hnot : y ≠ x + 2 := by
          intro h
          have heq : x + 1 = x + 2 := hrel.symm.trans h
          apply zModThree_add_one_ne x
          calc
            x = (x + 1) + 2 := by
              rw [add_assoc, show (1 + 2 : ZMod 3) = 0 by decide, add_zero]
            _ = (x + 2) + 2 := by rw [heq]
            _ = x + 1 := by
              rw [add_assoc, show (2 + 2 : ZMod 3) = 1 by decide]
        have hz : z = x - 1 := by
          calc
            z = (z + 1) - 1 := by ring
            _ = x - 1 := by rw [hzx]
        subst u
        subst z
        simp [mFiveFirstSecondFillTriangle, hor, hnot]
    · fin_cases j
      · have hix : (u, z + 2) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
      · have hix : (u, z + 2) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        apply False.elim
        apply hor
        have hu : u = a := congrArg Prod.fst hix
        calc
          threeLeaveOrientedPartner L a = threeLeaveOrientedPartner L u := by
            rw [hu]
          _ = b := congrArg Prod.fst hjy
      · have hix : (u, z + 2) = (a, x) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
        have hjy : (u, z + 2) = (b, y) := sumInr_inj
          (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
        exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))

private theorem mFiveFillTriangleIndex_eq_of_same_group_pair
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) (x y : ZMod 3) (hxy : x ≠ y)
    (q : α × ZMod 3)
    (hx : ∃ i : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) j = Sum.inr (a, y)) :
    Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) = mFiveFillTriangle L a x y := by
  rcases q with ⟨u, z⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  have sumInr_inj {p q : α × ZMod 3}
      (h : (Sum.inr p : Fin 5 ⊕ (α × ZMod 3)) = Sum.inr q) : p = q :=
    Sum.inr.inj h
  fin_cases i
  · fin_cases j
    · have hix : (u, z) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z) = (a, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact False.elim (hxy ((congrArg Prod.snd hix).symm.trans (congrArg Prod.snd hjy)))
    · have hix : (u, z) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (threeLeaveOrientedPartner L u, z + 1) = (a, y) :=
        sumInr_inj (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact False.elim (threeLeaveOrientedPartner_ne L u
        ((congrArg Prod.fst hjy).trans (congrArg Prod.fst hix).symm))
    · have hix : (u, z) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z + 2) = (a, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      have hu : u = a := congrArg Prod.fst hix
      have hz : z = x := congrArg Prod.snd hix
      have hrel : y = x + 2 := by
        calc
          y = z + 2 := (congrArg Prod.snd hjy).symm
          _ = x + 2 := by rw [hz]
      subst u
      subst z
      simp [mFiveFillTriangle, hrel]
  · fin_cases j
    · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) :=
        sumInr_inj (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z) = (a, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact False.elim (threeLeaveOrientedPartner_ne L u
        ((congrArg Prod.fst hix).trans (congrArg Prod.fst hjy).symm))
    · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) :=
        sumInr_inj (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (threeLeaveOrientedPartner L u, z + 1) = (a, y) :=
        sumInr_inj (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact False.elim (hxy ((congrArg Prod.snd hix).symm.trans (congrArg Prod.snd hjy)))
    · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) :=
        sumInr_inj (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z + 2) = (a, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact False.elim (threeLeaveOrientedPartner_ne L u
        ((congrArg Prod.fst hix).trans (congrArg Prod.fst hjy).symm))
  · fin_cases j
    · have hix : (u, z + 2) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z) = (a, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      have hu : u = a := congrArg Prod.fst hix
      have hzx : z + 2 = x := congrArg Prod.snd hix
      have hzy : z = y := congrArg Prod.snd hjy
      have hnot : y ≠ x + 2 := by
        intro h
        apply zModThree_add_one_ne z
        calc
          z = y := hzy
          _ = x + 2 := h
          _ = (z + 2) + 2 := by rw [hzx]
          _ = z + 1 := by
            rw [add_assoc, show (2 + 2 : ZMod 3) = 1 by decide]
      subst u
      subst z
      simp [mFiveFillTriangle, hnot]
    · have hix : (u, z + 2) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (threeLeaveOrientedPartner L u, z + 1) = (a, y) :=
        sumInr_inj (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact False.elim (threeLeaveOrientedPartner_ne L u
        ((congrArg Prod.fst hjy).trans (congrArg Prod.fst hix).symm))
    · have hix : (u, z + 2) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z + 2) = (a, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact False.elim (hxy ((congrArg Prod.snd hix).symm.trans (congrArg Prod.snd hjy)))

/-- The two group vertices of a first/second-leave residual triangle retain
the same fibre coordinate. -/
private theorem mFiveFirstSecondFactor_coordinates_eq_of_distinct_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2)
    (q : MatchingRepresentative (L.matching (mFiveFirstSecondMatching k)) × ZMod 3)
    (a b : α) (x y : ZMod 3) (hab : a ≠ b)
    (hx : ∃ i : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inl ⟨k, q⟩))) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inl ⟨k, q⟩))) j = Sum.inr (b, y)) :
    x = y := by
  rcases q with ⟨u, z⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  have sumInr_inj {p q : α × ZMod 3}
      (h : (Sum.inr p : Fin 5 ⊕ (α × ZMod 3)) = Sum.inr q) : p = q :=
    Sum.inr.inj h
  fin_cases i
  · simp [mFiveVertex] at hi
  · fin_cases j
    · simp [mFiveVertex] at hj
    · have hix : (u.1, z) = (a, x) :=
        sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjy : (u.1, z) = (b, y) :=
        sumInr_inj (by simpa [mFiveVertex] using hj)
      exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))
    · have hix : (u.1, z) = (a, x) :=
        sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjy : ((L.matching (mFiveFirstSecondMatching k)).perm u.1, z) = (b, y) :=
        sumInr_inj (by simpa [mFiveVertex] using hj)
      exact (congrArg Prod.snd hix).symm.trans (congrArg Prod.snd hjy)
  · fin_cases j
    · simp [mFiveVertex] at hj
    · have hix : ((L.matching (mFiveFirstSecondMatching k)).perm u.1, z) = (a, x) :=
        sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjy : (u.1, z) = (b, y) :=
        sumInr_inj (by simpa [mFiveVertex] using hj)
      exact (congrArg Prod.snd hix).symm.trans (congrArg Prod.snd hjy)
    · have hix : ((L.matching (mFiveFirstSecondMatching k)).perm u.1, z) = (a, x) :=
        sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjy : ((L.matching (mFiveFirstSecondMatching k)).perm u.1, z) = (b, y) :=
        sumInr_inj (by simpa [mFiveVertex] using hj)
      exact False.elim (hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy)))

/-- Distinct macro groups in an oriented fill triangle occur at different
points of their three-element fibres. -/
private theorem mFiveFill_coordinates_ne_of_distinct_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (q : α × ZMod 3)
    (a b : α) (x y : ZMod 3) (hab : a ≠ b)
    (hx : ∃ i : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) j = Sum.inr (b, y)) :
    x ≠ y := by
  intro hxy
  rcases q with ⟨u, z⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  have sumInr_inj {p q : α × ZMod 3}
      (h : (Sum.inr p : Fin 5 ⊕ (α × ZMod 3)) = Sum.inr q) : p = q :=
    Sum.inr.inj h
  fin_cases i
  · fin_cases j
    · have hix : (u, z) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy))
    · have hix : (u, z) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      apply zModThree_add_one_ne z
      calc
        z = x := congrArg Prod.snd hix
        _ = y := hxy
        _ = z + 1 := (congrArg Prod.snd hjy).symm
    · have hix : (u, z) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z + 2) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy))
  · fin_cases j
    · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      apply zModThree_add_one_ne z
      calc
        z = y := congrArg Prod.snd hjy
        _ = x := hxy.symm
        _ = z + 1 := (congrArg Prod.snd hix).symm
    · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy))
    · have hix : (threeLeaveOrientedPartner L u, z + 1) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z + 2) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      apply zModThree_add_one_ne (z + 1)
      calc
        z + 1 = x := congrArg Prod.snd hix
        _ = y := hxy
        _ = z + 2 := (congrArg Prod.snd hjy).symm
        _ = (z + 1) + 1 := by ring
  · fin_cases j
    · have hix : (u, z + 2) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy))
    · have hix : (u, z + 2) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (threeLeaveOrientedPartner L u, z + 1) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      apply zModThree_add_one_ne (z + 1)
      calc
        z + 1 = y := congrArg Prod.snd hjy
        _ = x := hxy.symm
        _ = z + 2 := (congrArg Prod.snd hix).symm
        _ = (z + 1) + 1 := by ring
    · have hix : (u, z + 2) = (a, x) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi)
      have hjy : (u, z + 2) = (b, y) := sumInr_inj
        (by simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj)
      exact hab ((congrArg Prod.fst hix).symm.trans (congrArg Prod.fst hjy))

/-- Away from the three matching leaves, a pair of distinct fibre labels can
occur only in the transversal above the corresponding macro triangle. -/
private theorem mFiveTriangle_eq_transversal_of_covers_nonmatching_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hnonmatching : ∀ r : Fin 3, (L.matching r).perm a ≠ b)
    (t : MFiveTriangleIndex L)
    (hx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (b, y)) :
    ∃ q : L.packing.Triangle × (ZMod 3 × ZMod 3),
      t = Sum.inr (Sum.inr (Sum.inr (Sum.inl q))) ∧
        (∃ i : Fin 3,
          mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) i = Sum.inr (a, x)) ∧
          ∃ j : Fin 3,
            mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases i <;> simp [mFiveVertex] at hi
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨r, u, z⟩
          have ha : a = u.1 ∨ a = (L.matching 2).perm u.1 := by
            fin_cases i
            · simp [mFiveVertex] at hi
            · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hi)).symm
            · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hi)).symm
          have hb : b = u.1 ∨ b = (L.matching 2).perm u.1 := by
            fin_cases j
            · simp [mFiveVertex] at hj
            · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hj)).symm
            · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hj)).symm
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact False.elim (hab (ha.trans hb.symm))
          · exact False.elim ((hnonmatching 2) (by
              calc
                (L.matching 2).perm a = (L.matching 2).perm u.1 := by rw [ha]
                _ = b := hb.symm))
          · exact False.elim ((hnonmatching 2) (by
              calc
                (L.matching 2).perm a = (L.matching 2).perm ((L.matching 2).perm u.1) := by
                  rw [ha]
                _ = u.1 := (L.matching 2).apply_apply u.1
                _ = b := hb.symm))
          · exact False.elim (hab (ha.trans hb.symm))
      | inr q =>
          cases q with
          | inl q =>
              rcases q with ⟨k, u, z⟩
              let M := L.matching (mFiveFirstSecondMatching k)
              have ha : a = u.1 ∨ a = M.perm u.1 := by
                fin_cases i
                · simp [mFiveVertex] at hi
                · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hi)).symm
                · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hi)).symm
              have hb : b = u.1 ∨ b = M.perm u.1 := by
                fin_cases j
                · simp [mFiveVertex] at hj
                · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hj)).symm
                · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hj)).symm
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · exact False.elim (hab (ha.trans hb.symm))
              · exact False.elim ((hnonmatching (mFiveFirstSecondMatching k)) (by
                  calc
                    (L.matching (mFiveFirstSecondMatching k)).perm a = M.perm u.1 := by
                      rw [ha]
                    _ = b := hb.symm))
              · exact False.elim ((hnonmatching (mFiveFirstSecondMatching k)) (by
                  calc
                    (L.matching (mFiveFirstSecondMatching k)).perm a = M.perm (M.perm u.1) := by
                      rw [ha]
                    _ = u.1 := M.apply_apply u.1
                    _ = b := hb.symm))
              · exact False.elim (hab (ha.trans hb.symm))
          | inr q =>
              cases q with
              | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
              | inr q =>
                  rcases q with ⟨u, z⟩
                  have ha : a = u ∨ a = threeLeaveOrientedPartner L u := by
                    fin_cases i
                    · have hix : u = a ∧ z = x := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi
                      exact Or.inl hix.1.symm
                    · have hix : threeLeaveOrientedPartner L u = a ∧ z + 1 = x := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi
                      exact Or.inr hix.1.symm
                    · have hix : u = a ∧ z + 2 = x := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi
                      exact Or.inl hix.1.symm
                  have hb : b = u ∨ b = threeLeaveOrientedPartner L u := by
                    fin_cases j
                    · have hjy : u = b ∧ z = y := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj
                      exact Or.inl hjy.1.symm
                    · have hjy : threeLeaveOrientedPartner L u = b ∧ z + 1 = y := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj
                      exact Or.inr hjy.1.symm
                    · have hjy : u = b ∧ z + 2 = y := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj
                      exact Or.inl hjy.1.symm
                  rcases ha with ha | ha <;> rcases hb with hb | hb
                  · exact False.elim (hab (ha.trans hb.symm))
                  · rcases threeLeaveOrientedPartner_matches L u with h0 | h1
                    · exact False.elim ((hnonmatching 0) (by
                        calc
                          (L.matching 0).perm a = (L.matching 0).perm u := by rw [ha]
                          _ = b := h0.symm.trans hb.symm))
                    · exact False.elim ((hnonmatching 1) (by
                        calc
                          (L.matching 1).perm a = (L.matching 1).perm u := by rw [ha]
                          _ = b := h1.symm.trans hb.symm))
                  · rcases threeLeaveOrientedPartner_matches L u with h0 | h1
                    · exact False.elim ((hnonmatching 0) (by
                        calc
                          (L.matching 0).perm a =
                              (L.matching 0).perm (threeLeaveOrientedPartner L u) := by rw [ha]
                          _ = (L.matching 0).perm ((L.matching 0).perm u) := by rw [h0]
                          _ = u := (L.matching 0).apply_apply u
                          _ = b := hb.symm))
                    · exact False.elim ((hnonmatching 1) (by
                        calc
                          (L.matching 1).perm a =
                              (L.matching 1).perm (threeLeaveOrientedPartner L u) := by rw [ha]
                          _ = (L.matching 1).perm ((L.matching 1).perm u) := by rw [h1]
                          _ = u := (L.matching 1).apply_apply u
                          _ = b := hb.symm))
                  · exact False.elim (hab (ha.trans hb.symm))

/-- The macro packing and the three-point transversal determine one literal
triangle through every pair outside the three matching leaves. -/
private theorem mFiveTransversalTriangleIndex_eq_of_distinct_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3) (hab : a ≠ b)
    (q q' : L.packing.Triangle × (ZMod 3 × ZMod 3))
    (hx : ∃ i : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inl q)))) j = Sum.inr (b, y))
    (hx' : ∃ i : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inl q')))) i = Sum.inr (a, x))
    (hy' : ∃ j : Fin 3,
      mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inl q')))) j = Sum.inr (b, y)) :
    q = q' := by
  rcases q with ⟨t, p⟩
  rcases q' with ⟨u, p'⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  rcases hx' with ⟨k, hk⟩
  rcases hy' with ⟨l, hl⟩
  have hai : L.packing.vertex t i = a := congrArg Prod.fst (Sum.inr.inj hi)
  have hbj : L.packing.vertex t j = b := congrArg Prod.fst (Sum.inr.inj hj)
  have hak : L.packing.vertex u k = a := congrArg Prod.fst (Sum.inr.inj hk)
  have hbl : L.packing.vertex u l = b := congrArg Prod.fst (Sum.inr.inj hl)
  have hix : (triplingCrossVertex p i).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [mFiveVertex] using hi))
  have hjy : (triplingCrossVertex p j).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [mFiveVertex] using hj))
  have hkx : (triplingCrossVertex p' k).2 = x :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [mFiveVertex] using hk))
  have hly : (triplingCrossVertex p' l).2 = y :=
    congrArg Prod.snd (Sum.inr.inj (by simpa only [mFiveVertex] using hl))
  have htu : t = u := L.packing.pair_covered_at_most_once a b hab t u
    ⟨i, hai⟩ ⟨j, hbj⟩ ⟨k, hak⟩ ⟨l, hbl⟩
  subst u
  have hik : i = k := L.packing.vertex_injective t (hai.trans hak.symm)
  have hjl : j = l := L.packing.vertex_injective t (hbj.trans hbl.symm)
  subst k
  subst l
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = L.packing.vertex t i := hai.symm
      _ = L.packing.vertex t j := by rw [hij]
      _ = b := hbj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p₀, hp₀, hp₀uniq⟩
  have hp :
      (∃ h : Fin 3, triplingCrossVertex p h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hix
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hjy
  have hp' :
      (∃ h : Fin 3, triplingCrossVertex p' h = (i, x)) ∧
        ∃ h : Fin 3, triplingCrossVertex p' h = (j, y) := by
    constructor
    · refine ⟨i, ?_⟩
      apply Prod.ext
      · fin_cases i <;> rfl
      · exact hkx
    · refine ⟨j, ?_⟩
      apply Prod.ext
      · fin_cases j <;> rfl
      · exact hly
  have hpp : p = p' := (hp₀uniq p hp).trans (hp₀uniq p' hp').symm
  subst p'
  rfl

/-- The third matching leaf selects the residual label from the signed
coordinate difference, with the sign determined by the fixed representative
of its unordered macro edge. -/
private def zModThreeToFin (z : ZMod 3) : Fin 3 := ⟨z.val, z.val_lt⟩

private theorem zModThreeToFin_cast (z : ZMod 3) :
    (zModThreeToFin z).1 = z :=
  ZMod.natCast_zmod_val z

private noncomputable def mFiveThirdMatchedFactorTriangle
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) (x y : ZMod 3) :
    MFiveTriangleIndex L :=
  let u := matchingRepresentative (L.matching 2) a
  let r : Fin 3 := if a = u.1 then zModThreeToFin (y - x) else zModThreeToFin (x - y)
  mFiveThirdFactorTriangle L r a x

private theorem mFiveThirdFactorTriangleIndex_eq_of_matched_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hmatching : (L.matching 2).perm a = b)
    (q : Σ r : Fin 3, MatchingRepresentative (L.matching 2) × ZMod 3)
    (hx : ∃ i : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (b, y)) :
    Sum.inr (Sum.inl q) = mFiveThirdMatchedFactorTriangle L a x y := by
  rcases q with ⟨r, u, z⟩
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  have sumInr_inj {p q : α × ZMod 3}
      (h : (Sum.inr p : Fin 5 ⊕ (α × ZMod 3)) = Sum.inr q) : p = q :=
    Sum.inr.inj h
  fin_cases i
  · simp [mFiveVertex] at hi
  · fin_cases j
    · simp [mFiveVertex] at hj
    · have hia : (u.1, z) = (a, x) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjb : (u.1, z) = (b, y) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hj)
      exact False.elim (hab ((congrArg Prod.fst hia).symm.trans (congrArg Prod.fst hjb)))
    · have hia : (u.1, z) = (a, x) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjb : ((L.matching 2).perm u.1, z + (r.1 : ZMod 3)) = (b, y) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hj)
      have hu : u.1 = a := congrArg Prod.fst hia
      have hz : z = x := congrArg Prod.snd hia
      have hcoord : z + (r.1 : ZMod 3) = y := congrArg Prod.snd hjb
      have hdiff : (r.1 : ZMod 3) = y - x := by
        calc
          (r.1 : ZMod 3) = z + (r.1 : ZMod 3) - z := by ring
          _ = y - x := by rw [hcoord, hz]
      have hval : (zModThreeToFin (y - x)).1 = y - x := zModThreeToFin_cast _
      have hr : r = zModThreeToFin (y - x) := by
        apply Fin.ext
        have hcast : (r.1 : ZMod 3) = (zModThreeToFin (y - x)).1 := hdiff.trans hval.symm
        have hcastval := congrArg ZMod.val hcast
        have hleft : r.1 % 3 = r.1 := Nat.mod_eq_of_lt r.isLt
        have hright : (zModThreeToFin (y - x)).1 % 3 = (zModThreeToFin (y - x)).1 :=
          Nat.mod_eq_of_lt (zModThreeToFin (y - x)).isLt
        simpa only [ZMod.val_natCast, hleft, hright] using hcastval
      subst r
      have hrep : matchingRepresentative (L.matching 2) a = u :=
        matchingRepresentative_eq_of_endpoint _ u a (Or.inl hu.symm)
      have hfirst : a = (matchingRepresentative (L.matching 2) a).1 := by
        calc
          a = u.1 := hu.symm
          _ = (matchingRepresentative (L.matching 2) a).1 := congrArg Subtype.val hrep.symm
      calc
        Sum.inr (Sum.inl ⟨zModThreeToFin (y - x), u, z⟩) =
            mFiveThirdFactorTriangle L (zModThreeToFin (y - x)) a x :=
          mFiveThirdFactorTriangleIndex_eq_of_residual_group L (zModThreeToFin (y - x)) a x
            ⟨zModThreeToFin (y - x), u, z⟩ ⟨0, by simp [mFiveVertex]⟩ ⟨1, hi⟩
        _ = mFiveThirdMatchedFactorTriangle L a x y := by
          unfold mFiveThirdMatchedFactorTriangle
          dsimp
          rw [if_pos hfirst]
  · fin_cases j
    · simp [mFiveVertex] at hj
    · have hia : ((L.matching 2).perm u.1, z + (r.1 : ZMod 3)) = (a, x) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjb : (u.1, z) = (b, y) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hj)
      have hu : (L.matching 2).perm u.1 = a := congrArg Prod.fst hia
      have hz : z = y := congrArg Prod.snd hjb
      have hcoord : z + (r.1 : ZMod 3) = x := congrArg Prod.snd hia
      have hdiff : (r.1 : ZMod 3) = x - y := by
        calc
          (r.1 : ZMod 3) = z + (r.1 : ZMod 3) - z := by ring
          _ = x - y := by rw [hcoord, hz]
      have hval : (zModThreeToFin (x - y)).1 = x - y := zModThreeToFin_cast _
      have hr : r = zModThreeToFin (x - y) := by
        apply Fin.ext
        have hcast : (r.1 : ZMod 3) = (zModThreeToFin (x - y)).1 := hdiff.trans hval.symm
        have hcastval := congrArg ZMod.val hcast
        have hleft : r.1 % 3 = r.1 := Nat.mod_eq_of_lt r.isLt
        have hright : (zModThreeToFin (x - y)).1 % 3 = (zModThreeToFin (x - y)).1 :=
          Nat.mod_eq_of_lt (zModThreeToFin (x - y)).isLt
        simpa only [ZMod.val_natCast, hleft, hright] using hcastval
      subst r
      have hrep : matchingRepresentative (L.matching 2) a = u :=
        matchingRepresentative_eq_of_endpoint _ u a (Or.inr hu.symm)
      have hnot : a ≠ (matchingRepresentative (L.matching 2) a).1 := by
        intro h
        apply (L.matching 2).apply_ne u.1
        calc
          (L.matching 2).perm u.1 = a := hu
          _ = (matchingRepresentative (L.matching 2) a).1 := h
          _ = u.1 := congrArg Subtype.val hrep
      calc
        Sum.inr (Sum.inl ⟨zModThreeToFin (x - y), u, z⟩) =
            mFiveThirdFactorTriangle L (zModThreeToFin (x - y)) a x :=
          mFiveThirdFactorTriangleIndex_eq_of_residual_group L (zModThreeToFin (x - y)) a x
            ⟨zModThreeToFin (x - y), u, z⟩ ⟨0, by simp [mFiveVertex]⟩ ⟨2, hi⟩
        _ = mFiveThirdMatchedFactorTriangle L a x y := by
          unfold mFiveThirdMatchedFactorTriangle
          dsimp
          rw [if_neg hnot]
    · have hia : ((L.matching 2).perm u.1, z + (r.1 : ZMod 3)) = (a, x) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hi)
      have hjb : ((L.matching 2).perm u.1, z + (r.1 : ZMod 3)) = (b, y) := by
        exact sumInr_inj (by simpa [mFiveVertex] using hj)
      exact False.elim (hab ((congrArg Prod.fst hia).symm.trans (congrArg Prod.fst hjb)))

/-- A pair of macro labels joined by the third leave occurs only in the
corresponding third-leave residual triangle. -/
private theorem mFiveTriangle_eq_third_factor_of_covers_third_matching_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hmatching : (L.matching 2).perm a = b)
    (t : MFiveTriangleIndex L)
    (hx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (b, y)) :
    ∃ q : Σ r : Fin 3, MatchingRepresentative (L.matching 2) × ZMod 3,
      t = Sum.inr (Sum.inl q) ∧
        (∃ i : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) i = Sum.inr (a, x)) ∧
          ∃ j : Fin 3, mFiveVertex L (Sum.inr (Sum.inl q)) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases i <;> simp [mFiveVertex] at hi
  | inr q =>
      cases q with
      | inl q => exact ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
      | inr q =>
          cases q with
          | inl q =>
              rcases q with ⟨k, u, z⟩
              let M := L.matching (mFiveFirstSecondMatching k)
              have hk2 : mFiveFirstSecondMatching k ≠ 2 := by
                fin_cases k <;> decide
              have ha : a = u.1 ∨ a = M.perm u.1 := by
                fin_cases i
                · simp [mFiveVertex] at hi
                · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hi)).symm
                · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hi)).symm
              have hb : b = u.1 ∨ b = M.perm u.1 := by
                fin_cases j
                · simp [mFiveVertex] at hj
                · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hj)).symm
                · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hj)).symm
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · exact False.elim (hab (ha.trans hb.symm))
              · have hMk : (L.matching (mFiveFirstSecondMatching k)).perm a = b := by
                  calc
                    (L.matching (mFiveFirstSecondMatching k)).perm a = M.perm u.1 := by rw [ha]
                    _ = b := hb.symm
                exact False.elim (L.matching_edges_disjoint (mFiveFirstSecondMatching k) 2 hk2 a
                  (hMk.trans hmatching.symm))
              · have hMk : (L.matching (mFiveFirstSecondMatching k)).perm a = b := by
                  calc
                    (L.matching (mFiveFirstSecondMatching k)).perm a = M.perm (M.perm u.1) := by
                      rw [ha]
                    _ = u.1 := M.apply_apply u.1
                    _ = b := hb.symm
                exact False.elim (L.matching_edges_disjoint (mFiveFirstSecondMatching k) 2 hk2 a
                  (hMk.trans hmatching.symm))
              · exact False.elim (hab (ha.trans hb.symm))
          | inr q =>
              cases q with
              | inl q =>
                  rcases q with ⟨u, z⟩
                  have hcover : L.packing.CoversPair a b :=
                    ⟨u, ⟨i, congrArg Prod.fst (Sum.inr.inj hi)⟩,
                      ⟨j, congrArg Prod.fst (Sum.inr.inj hj)⟩⟩
                  exact False.elim ((L.coversPair_iff a b hab).mp hcover 2 hmatching)
              | inr q =>
                  rcases q with ⟨u, z⟩
                  have ha : a = u ∨ a = threeLeaveOrientedPartner L u := by
                    fin_cases i
                    · have hix : u = a ∧ z = x := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi
                      exact Or.inl hix.1.symm
                    · have hix : threeLeaveOrientedPartner L u = a ∧ z + 1 = x := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi
                      exact Or.inr hix.1.symm
                    · have hix : u = a ∧ z + 2 = x := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hi
                      exact Or.inl hix.1.symm
                  have hb : b = u ∨ b = threeLeaveOrientedPartner L u := by
                    fin_cases j
                    · have hjy : u = b ∧ z = y := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj
                      exact Or.inl hjy.1.symm
                    · have hjy : threeLeaveOrientedPartner L u = b ∧ z + 1 = y := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj
                      exact Or.inr hjy.1.symm
                    · have hjy : u = b ∧ z + 2 = y := by
                        simpa [mFiveVertex, threeMatchingLeaveMacroVertex] using hj
                      exact Or.inl hjy.1.symm
                  rcases ha with ha | ha <;> rcases hb with hb | hb
                  · exact False.elim (hab (ha.trans hb.symm))

                  · rcases threeLeaveOrientedPartner_matches L u with h0 | h1
                    · have hM : (L.matching 0).perm a = b := by
                        calc
                          (L.matching 0).perm a = (L.matching 0).perm u := by rw [ha]
                          _ = b := h0.symm.trans hb.symm
                      exact False.elim (L.matching_edges_disjoint 0 2 (by decide) a
                        (hM.trans hmatching.symm))
                    · have hM : (L.matching 1).perm a = b := by
                        calc
                          (L.matching 1).perm a = (L.matching 1).perm u := by rw [ha]
                          _ = b := h1.symm.trans hb.symm
                      exact False.elim (L.matching_edges_disjoint 1 2 (by decide) a
                        (hM.trans hmatching.symm))
                  · rcases threeLeaveOrientedPartner_matches L u with h0 | h1
                    · have hM : (L.matching 0).perm a = b := by
                        calc
                          (L.matching 0).perm a =
                              (L.matching 0).perm (threeLeaveOrientedPartner L u) := by rw [ha]
                          _ = (L.matching 0).perm ((L.matching 0).perm u) := by rw [h0]
                          _ = u := (L.matching 0).apply_apply u
                          _ = b := hb.symm
                      exact False.elim (L.matching_edges_disjoint 0 2 (by decide) a
                        (hM.trans hmatching.symm))
                    · have hM : (L.matching 1).perm a = b := by
                        calc
                          (L.matching 1).perm a =
                              (L.matching 1).perm (threeLeaveOrientedPartner L u) := by rw [ha]
                          _ = (L.matching 1).perm ((L.matching 1).perm u) := by rw [h1]
                          _ = u := (L.matching 1).apply_apply u
                          _ = b := hb.symm
                      exact False.elim (L.matching_edges_disjoint 1 2 (by decide) a
                        (hM.trans hmatching.symm))
                  · exact False.elim (hab (ha.trans hb.symm))

private theorem mFiveThirdMatching_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hmatching : (L.matching 2).perm a = b)
    (t u : MFiveTriangleIndex L)
    (htx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hty : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (b, y))
    (hux : ∃ i : Fin 3, mFiveVertex L u i = Sum.inr (a, x))
    (huy : ∃ j : Fin 3, mFiveVertex L u j = Sum.inr (b, y)) :
    t = u := by
  rcases mFiveTriangle_eq_third_factor_of_covers_third_matching_groups
    L a b x y hab hmatching t htx hty with ⟨q, hq, hqx, hqy⟩
  rcases mFiveTriangle_eq_third_factor_of_covers_third_matching_groups
    L a b x y hab hmatching u hux huy with ⟨q', hq', hq'x, hq'y⟩
  have hcanon : Sum.inr (Sum.inl q) = mFiveThirdMatchedFactorTriangle L a x y :=
    mFiveThirdFactorTriangleIndex_eq_of_matched_groups L a b x y hab hmatching q hqx hqy
  have hcanon' : Sum.inr (Sum.inl q') = mFiveThirdMatchedFactorTriangle L a x y :=
    mFiveThirdFactorTriangleIndex_eq_of_matched_groups L a b x y hab hmatching q' hq'x hq'y
  calc
    t = Sum.inr (Sum.inl q) := hq
    _ = Sum.inr (Sum.inl q') := hcanon.trans hcanon'.symm
    _ = u := hq'.symm

/-- A pair on either of the first two matching leaves is contained either in
its residual factor triangle or in one oriented fill triangle. -/
private theorem mFiveTriangle_eq_firstSecond_factor_or_fill_of_covers_matching_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a b : α)
    (x y : ZMod 3) (hab : a ≠ b)
    (hmatching : (L.matching (mFiveFirstSecondMatching k)).perm a = b)
    (t : MFiveTriangleIndex L)
    (hx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hy : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (b, y)) :
    (∃ q : MatchingRepresentative (L.matching (mFiveFirstSecondMatching k)) × ZMod 3,
      t = Sum.inr (Sum.inr (Sum.inl ⟨k, q⟩)) ∧
        (∃ i : Fin 3, mFiveVertex L (Sum.inr (Sum.inr (Sum.inl ⟨k, q⟩))) i =
          Sum.inr (a, x)) ∧
          ∃ j : Fin 3, mFiveVertex L (Sum.inr (Sum.inr (Sum.inl ⟨k, q⟩))) j =
            Sum.inr (b, y)) ∨
      ∃ q : α × ZMod 3,
        t = Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) ∧
          (∃ i : Fin 3,
            mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) i = Sum.inr (a, x)) ∧
            ∃ j : Fin 3,
              mFiveVertex L (Sum.inr (Sum.inr (Sum.inr (Sum.inr q)))) j = Sum.inr (b, y) := by
  rcases hx with ⟨i, hi⟩
  rcases hy with ⟨j, hj⟩
  cases t with
  | inl p => fin_cases i <;> simp [mFiveVertex] at hi
  | inr q =>
      cases q with
      | inl q =>
          rcases q with ⟨r, u, z⟩
          have ha : a = u.1 ∨ a = (L.matching 2).perm u.1 := by
            fin_cases i
            · simp [mFiveVertex] at hi
            · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hi)).symm
            · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hi)).symm
          have hb : b = u.1 ∨ b = (L.matching 2).perm u.1 := by
            fin_cases j
            · simp [mFiveVertex] at hj
            · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hj)).symm
            · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hj)).symm
          have hindex : (2 : Fin 3) ≠ mFiveFirstSecondMatching k := by
            fin_cases k <;> decide
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact False.elim (hab (ha.trans hb.symm))
          · have hM : (L.matching 2).perm a = b := by
              calc
                (L.matching 2).perm a = (L.matching 2).perm u.1 := by rw [ha]
                _ = b := hb.symm
            exact False.elim (L.matching_edges_disjoint 2 (mFiveFirstSecondMatching k) hindex a
              (hM.trans hmatching.symm))
          · have hM : (L.matching 2).perm a = b := by
              calc
                (L.matching 2).perm a = (L.matching 2).perm ((L.matching 2).perm u.1) := by
                  rw [ha]
                _ = u.1 := (L.matching 2).apply_apply u.1
                _ = b := hb.symm
            exact False.elim (L.matching_edges_disjoint 2 (mFiveFirstSecondMatching k) hindex a
              (hM.trans hmatching.symm))
          · exact False.elim (hab (ha.trans hb.symm))
      | inr q =>
          cases q with
          | inl q =>
              rcases q with ⟨k', u, z⟩
              let M := L.matching (mFiveFirstSecondMatching k')
              have ha : a = u.1 ∨ a = M.perm u.1 := by
                fin_cases i
                · simp [mFiveVertex] at hi
                · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hi)).symm
                · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hi)).symm
              have hb : b = u.1 ∨ b = M.perm u.1 := by
                fin_cases j
                · simp [mFiveVertex] at hj
                · exact Or.inl (congrArg Prod.fst (Sum.inr.inj hj)).symm
                · exact Or.inr (congrArg Prod.fst (Sum.inr.inj hj)).symm
              have hindex_of_ne (hk : k' ≠ k) :
                  mFiveFirstSecondMatching k' ≠ mFiveFirstSecondMatching k := by
                intro hindex
                apply hk
                apply Fin.ext
                simpa [mFiveFirstSecondMatching] using congrArg Fin.val hindex
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · exact False.elim (hab (ha.trans hb.symm))
              · have hM : (L.matching (mFiveFirstSecondMatching k')).perm a = b := by
                  calc
                    (L.matching (mFiveFirstSecondMatching k')).perm a = M.perm u.1 := by rw [ha]
                    _ = b := hb.symm
                by_cases hk : k' = k
                · subst k'
                  exact Or.inl ⟨(u, z), rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
                · exact False.elim (L.matching_edges_disjoint
                    (mFiveFirstSecondMatching k') (mFiveFirstSecondMatching k) (hindex_of_ne hk) a
                    (hM.trans hmatching.symm))
              · have hM : (L.matching (mFiveFirstSecondMatching k')).perm a = b := by
                  calc
                    (L.matching (mFiveFirstSecondMatching k')).perm a = M.perm (M.perm u.1) := by
                      rw [ha]
                    _ = u.1 := M.apply_apply u.1
                    _ = b := hb.symm
                by_cases hk : k' = k
                · subst k'
                  exact Or.inl ⟨(u, z), rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩
                · exact False.elim (L.matching_edges_disjoint
                    (mFiveFirstSecondMatching k') (mFiveFirstSecondMatching k) (hindex_of_ne hk) a
                    (hM.trans hmatching.symm))
              · exact False.elim (hab (ha.trans hb.symm))
          | inr q =>
              cases q with
              | inl q =>
                  rcases q with ⟨u, z⟩
                  have hcover : L.packing.CoversPair a b :=
                    ⟨u, ⟨i, congrArg Prod.fst (Sum.inr.inj hi)⟩,
                      ⟨j, congrArg Prod.fst (Sum.inr.inj hj)⟩⟩
                  exact False.elim ((L.coversPair_iff a b hab).mp hcover
                    (mFiveFirstSecondMatching k) hmatching)
              | inr q => exact Or.inr ⟨q, rfl, ⟨i, hi⟩, ⟨j, hj⟩⟩

/-- Every pair on one of the first two matching leaves is covered by at most
one literal triangle of the five-residual-vertex construction. -/
private theorem mFiveFirstSecondMatching_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a b : α)
    (x y : ZMod 3) (hab : a ≠ b)
    (hmatching : (L.matching (mFiveFirstSecondMatching k)).perm a = b)
    (t u : MFiveTriangleIndex L)
    (htx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hty : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (b, y))
    (hux : ∃ i : Fin 3, mFiveVertex L u i = Sum.inr (a, x))
    (huy : ∃ j : Fin 3, mFiveVertex L u j = Sum.inr (b, y)) :
    t = u := by
  by_cases hxy : x = y
  · have ht : t = mFiveFirstSecondFactorTriangle L k a x := by
      rcases mFiveTriangle_eq_firstSecond_factor_or_fill_of_covers_matching_groups
        L k a b x y hab hmatching t htx hty with hfactor | hfill
      · rcases hfactor with ⟨q, hq, hqx, hqy⟩
        calc
          t = Sum.inr (Sum.inr (Sum.inl ⟨k, q⟩)) := hq
          _ = mFiveFirstSecondFactorTriangle L k a x :=
            mFiveFirstSecondFactorTriangleIndex_eq_of_residual_group L k a x ⟨k, q⟩
              ⟨0, by simp [mFiveVertex]⟩ hqx
      · rcases hfill with ⟨q, hq, hqx, hqy⟩
        exact False.elim (mFiveFill_coordinates_ne_of_distinct_groups L q a b x y hab hqx hqy hxy)
    have hu : u = mFiveFirstSecondFactorTriangle L k a x := by
      rcases mFiveTriangle_eq_firstSecond_factor_or_fill_of_covers_matching_groups
        L k a b x y hab hmatching u hux huy with hfactor | hfill
      · rcases hfactor with ⟨q, hq, hqx, hqy⟩
        calc
          u = Sum.inr (Sum.inr (Sum.inl ⟨k, q⟩)) := hq
          _ = mFiveFirstSecondFactorTriangle L k a x :=
            mFiveFirstSecondFactorTriangleIndex_eq_of_residual_group L k a x ⟨k, q⟩
              ⟨0, by simp [mFiveVertex]⟩ hqx
      · rcases hfill with ⟨q, hq, hqx, hqy⟩
        exact False.elim (mFiveFill_coordinates_ne_of_distinct_groups L q a b x y hab hqx hqy hxy)
    exact ht.trans hu.symm
  · have ht : t = mFiveFirstSecondFillTriangle L a b x y := by
      rcases mFiveTriangle_eq_firstSecond_factor_or_fill_of_covers_matching_groups
        L k a b x y hab hmatching t htx hty with hfactor | hfill
      · rcases hfactor with ⟨q, hq, hqx, hqy⟩
        exact False.elim (hxy
          (mFiveFirstSecondFactor_coordinates_eq_of_distinct_groups L k q a b x y hab hqx hqy))
      · rcases hfill with ⟨q, hq, hqx, hqy⟩
        calc
          t = Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) := hq
          _ = mFiveFirstSecondFillTriangle L a b x y :=
            mFiveFirstSecondFillTriangleIndex_eq_of_matched_groups L k a b x y hab hmatching q hqx hqy
    have hu : u = mFiveFirstSecondFillTriangle L a b x y := by
      rcases mFiveTriangle_eq_firstSecond_factor_or_fill_of_covers_matching_groups
        L k a b x y hab hmatching u hux huy with hfactor | hfill
      · rcases hfactor with ⟨q, hq, hqx, hqy⟩
        exact False.elim (hxy
          (mFiveFirstSecondFactor_coordinates_eq_of_distinct_groups L k q a b x y hab hqx hqy))
      · rcases hfill with ⟨q, hq, hqx, hqy⟩
        calc
          u = Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) := hq
          _ = mFiveFirstSecondFillTriangle L a b x y :=
            mFiveFirstSecondFillTriangleIndex_eq_of_matched_groups L k a b x y hab hmatching q hqx hqy
    exact ht.trans hu.symm

/-- A pair of distinct macro groups outside all three matching leaves occurs
in at most one transversal triangle. -/
private theorem mFiveNonmatching_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hnonmatching : ∀ r : Fin 3, (L.matching r).perm a ≠ b)
    (t u : MFiveTriangleIndex L)
    (htx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hty : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (b, y))
    (hux : ∃ i : Fin 3, mFiveVertex L u i = Sum.inr (a, x))
    (huy : ∃ j : Fin 3, mFiveVertex L u j = Sum.inr (b, y)) :
    t = u := by
  rcases mFiveTriangle_eq_transversal_of_covers_nonmatching_groups
    L a b x y hab hnonmatching t htx hty with ⟨q, hq, hqx, hqy⟩
  rcases mFiveTriangle_eq_transversal_of_covers_nonmatching_groups
    L a b x y hab hnonmatching u hux huy with ⟨q', hq', hq'x, hq'y⟩
  have hqq' : q = q' :=
    mFiveTransversalTriangleIndex_eq_of_distinct_groups L a b x y hab q q' hqx hqy hq'x hq'y
  calc
    t = Sum.inr (Sum.inr (Sum.inr (Sum.inl q))) := hq
    _ = Sum.inr (Sum.inr (Sum.inr (Sum.inl q'))) := congrArg
      (fun z => Sum.inr (Sum.inr (Sum.inr (Sum.inl z)))) hqq'
    _ = u := hq'.symm

/-- Two different fibre points in one macro group occur in at most one
oriented fill triangle. -/
private theorem mFiveSameGroup_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) (x y : ZMod 3)
    (hxy : x ≠ y) (t u : MFiveTriangleIndex L)
    (htx : ∃ i : Fin 3, mFiveVertex L t i = Sum.inr (a, x))
    (hty : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (a, y))
    (hux : ∃ i : Fin 3, mFiveVertex L u i = Sum.inr (a, x))
    (huy : ∃ j : Fin 3, mFiveVertex L u j = Sum.inr (a, y)) :
    t = u := by
  rcases mFiveTriangle_eq_fill_of_covers_same_group_pair L a x y hxy t htx hty with
    ⟨q, hq, hqx, hqy⟩
  rcases mFiveTriangle_eq_fill_of_covers_same_group_pair L a x y hxy u hux huy with
    ⟨q', hq', hq'x, hq'y⟩
  have hcanon : Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) = mFiveFillTriangle L a x y :=
    mFiveFillTriangleIndex_eq_of_same_group_pair L a x y hxy q hqx hqy
  have hcanon' : Sum.inr (Sum.inr (Sum.inr (Sum.inr q'))) = mFiveFillTriangle L a x y :=
    mFiveFillTriangleIndex_eq_of_same_group_pair L a x y hxy q' hq'x hq'y
  calc
    t = Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) := hq
    _ = Sum.inr (Sum.inr (Sum.inr (Sum.inr q'))) := hcanon.trans hcanon'.symm
    _ = u := hq'.symm

/-- A designated third-matching residual vertex and a fibre point select one
literal factor triangle. -/
private theorem mFiveThirdResidualGroup_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 3) (a : α) (x : ZMod 3)
    (t u : MFiveTriangleIndex L)
    (htr : ∃ i : Fin 3, mFiveVertex L t i = Sum.inl (mFiveThirdResidual r))
    (htx : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (a, x))
    (hur : ∃ i : Fin 3, mFiveVertex L u i = Sum.inl (mFiveThirdResidual r))
    (hux : ∃ j : Fin 3, mFiveVertex L u j = Sum.inr (a, x)) :
    t = u := by
  have hnot : ∀ k : Fin 2, mFiveFirstSecondResidual k ≠ mFiveThirdResidual r := by
    intro k h
    fin_cases k <;> fin_cases r <;> simp [mFiveFirstSecondResidual, mFiveThirdResidual] at h
  have ht : t = mFiveThirdFactorTriangle L r a x := by
    rcases mFiveTriangle_eq_matching_of_covers_residual_group L (mFiveThirdResidual r) a x t htr htx
      with hthird | hfirst
    · rcases hthird with ⟨q, hq, hqr, hqx⟩
      calc
        t = Sum.inr (Sum.inl q) := hq
        _ = mFiveThirdFactorTriangle L r a x :=
          mFiveThirdFactorTriangleIndex_eq_of_residual_group L r a x q hqr hqx
    · rcases hfirst with ⟨q, hq, hqr, hqx⟩
      rcases q with ⟨k, v, z⟩
      rcases hqr with ⟨i, hi⟩
      fin_cases i
      · have hsum : (Sum.inl (mFiveFirstSecondResidual k) : Fin 5 ⊕ (α × ZMod 3)) =
            Sum.inl (mFiveThirdResidual r) := by
            simpa [mFiveVertex] using hi
        have hres : mFiveFirstSecondResidual k = mFiveThirdResidual r := Sum.inl.inj hsum
        exact False.elim (hnot k hres)
      · simp [mFiveVertex] at hi
      · simp [mFiveVertex] at hi
  have hu : u = mFiveThirdFactorTriangle L r a x := by
    rcases mFiveTriangle_eq_matching_of_covers_residual_group L (mFiveThirdResidual r) a x u hur hux
      with hthird | hfirst
    · rcases hthird with ⟨q, hq, hqr, hqx⟩
      calc
        u = Sum.inr (Sum.inl q) := hq
        _ = mFiveThirdFactorTriangle L r a x :=
          mFiveThirdFactorTriangleIndex_eq_of_residual_group L r a x q hqr hqx
    · rcases hfirst with ⟨q, hq, hqr, hqx⟩
      rcases q with ⟨k, v, z⟩
      rcases hqr with ⟨i, hi⟩
      fin_cases i
      · have hsum : (Sum.inl (mFiveFirstSecondResidual k) : Fin 5 ⊕ (α × ZMod 3)) =
            Sum.inl (mFiveThirdResidual r) := by
            simpa [mFiveVertex] using hi
        have hres : mFiveFirstSecondResidual k = mFiveThirdResidual r := Sum.inl.inj hsum
        exact False.elim (hnot k hres)
      · simp [mFiveVertex] at hi
      · simp [mFiveVertex] at hi
  exact ht.trans hu.symm

/-- A designated first- or second-matching residual vertex and a fibre point
select one literal factor triangle. -/
private theorem mFiveFirstSecondResidualGroup_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a : α) (x : ZMod 3)
    (t u : MFiveTriangleIndex L)
    (htr : ∃ i : Fin 3, mFiveVertex L t i = Sum.inl (mFiveFirstSecondResidual k))
    (htx : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (a, x))
    (hur : ∃ i : Fin 3, mFiveVertex L u i = Sum.inl (mFiveFirstSecondResidual k))
    (hux : ∃ j : Fin 3, mFiveVertex L u j = Sum.inr (a, x)) :
    t = u := by
  have hnot : ∀ r : Fin 3, mFiveThirdResidual r ≠ mFiveFirstSecondResidual k := by
    intro r h
    fin_cases r <;> fin_cases k <;> simp [mFiveFirstSecondResidual, mFiveThirdResidual] at h
  have ht : t = mFiveFirstSecondFactorTriangle L k a x := by
    rcases mFiveTriangle_eq_matching_of_covers_residual_group L (mFiveFirstSecondResidual k) a x t htr htx
      with hthird | hfirst
    · rcases hthird with ⟨q, hq, hqr, hqx⟩
      rcases q with ⟨r, v, z⟩
      rcases hqr with ⟨i, hi⟩
      fin_cases i
      · have hsum : (Sum.inl (mFiveThirdResidual r) : Fin 5 ⊕ (α × ZMod 3)) =
            Sum.inl (mFiveFirstSecondResidual k) := by
            simpa [mFiveVertex] using hi
        have hres : mFiveThirdResidual r = mFiveFirstSecondResidual k := Sum.inl.inj hsum
        exact False.elim (hnot r hres)
      · simp [mFiveVertex] at hi
      · simp [mFiveVertex] at hi
    · rcases hfirst with ⟨q, hq, hqr, hqx⟩
      calc
        t = Sum.inr (Sum.inr (Sum.inl q)) := hq
        _ = mFiveFirstSecondFactorTriangle L k a x :=
          mFiveFirstSecondFactorTriangleIndex_eq_of_residual_group L k a x q hqr hqx
  have hu : u = mFiveFirstSecondFactorTriangle L k a x := by
    rcases mFiveTriangle_eq_matching_of_covers_residual_group L (mFiveFirstSecondResidual k) a x u hur hux
      with hthird | hfirst
    · rcases hthird with ⟨q, hq, hqr, hqx⟩
      rcases q with ⟨r, v, z⟩
      rcases hqr with ⟨i, hi⟩
      fin_cases i
      · have hsum : (Sum.inl (mFiveThirdResidual r) : Fin 5 ⊕ (α × ZMod 3)) =
            Sum.inl (mFiveFirstSecondResidual k) := by
            simpa [mFiveVertex] using hi
        have hres : mFiveThirdResidual r = mFiveFirstSecondResidual k := Sum.inl.inj hsum
        exact False.elim (hnot r hres)
      · simp [mFiveVertex] at hi
      · simp [mFiveVertex] at hi
    · rcases hfirst with ⟨q, hq, hqr, hqx⟩
      calc
        u = Sum.inr (Sum.inr (Sum.inl q)) := hq
        _ = mFiveFirstSecondFactorTriangle L k a x :=
          mFiveFirstSecondFactorTriangleIndex_eq_of_residual_group L k a x q hqr hqx
  exact ht.trans hu.symm

/-- Every residual/fibre pair in the five-residual construction is covered by
at most one literal triangle. -/
private theorem mFiveResidualGroup_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 5) (a : α) (x : ZMod 3)
    (t u : MFiveTriangleIndex L)
    (htr : ∃ i : Fin 3, mFiveVertex L t i = Sum.inl r)
    (htx : ∃ j : Fin 3, mFiveVertex L t j = Sum.inr (a, x))
    (hur : ∃ i : Fin 3, mFiveVertex L u i = Sum.inl r)
    (hux : ∃ j : Fin 3, mFiveVertex L u j = Sum.inr (a, x)) :
    t = u := by
  fin_cases r
  · apply mFiveThirdResidualGroup_pair_covered_at_most_once L 0 a x t u
    · simpa [mFiveThirdResidual] using htr
    · exact htx
    · simpa [mFiveThirdResidual] using hur
    · exact hux
  · apply mFiveThirdResidualGroup_pair_covered_at_most_once L 1 a x t u
    · simpa [mFiveThirdResidual] using htr
    · exact htx
    · simpa [mFiveThirdResidual] using hur
    · exact hux
  · apply mFiveThirdResidualGroup_pair_covered_at_most_once L 2 a x t u
    · simpa [mFiveThirdResidual] using htr
    · exact htx
    · simpa [mFiveThirdResidual] using hur
    · exact hux
  · apply mFiveFirstSecondResidualGroup_pair_covered_at_most_once L 0 a x t u
    · simpa [mFiveFirstSecondResidual] using htr
    · exact htx
    · simpa [mFiveFirstSecondResidual] using hur
    · exact hux
  · apply mFiveFirstSecondResidualGroup_pair_covered_at_most_once L 1 a x t u
    · simpa [mFiveFirstSecondResidual] using htr
    · exact htx
    · simpa [mFiveFirstSecondResidual] using hur
    · exact hux

private theorem mFivePacking_pair_covered_at_most_once
    (L : TrianglePacking.WithThreeMatchingLeaves α) :
    ∀ p q : Fin 5 ⊕ (α × ZMod 3), p ≠ q →
      ∀ t u : MFiveTriangleIndex L,
        (∃ i : Fin 3, mFiveVertex L t i = p) →
        (∃ j : Fin 3, mFiveVertex L t j = q) →
        (∃ i : Fin 3, mFiveVertex L u i = p) →
        (∃ j : Fin 3, mFiveVertex L u j = q) → t = u := by
  rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hpq t u htp htq hup huq
  · have hrs : r ≠ s := by
      intro hrs
      apply hpq
      rw [hrs]
    rcases mFiveTriangle_eq_residual_of_covers_two_residual L r s hrs t htp htq with
      ⟨v, hv, hvr, hvs⟩
    rcases mFiveTriangle_eq_residual_of_covers_two_residual L r s hrs u hup huq with
      ⟨w, hw, hwr, hws⟩
    calc
      t = Sum.inl v := hv
      _ = Sum.inl w := congrArg Sum.inl
        (finFive.pair_covered_at_most_once r s hrs v w hvr hvs hwr hws)
      _ = u := hw.symm
  · exact mFiveResidualGroup_pair_covered_at_most_once L r b y t u htp htq hup huq
  · exact mFiveResidualGroup_pair_covered_at_most_once L s a x t u htq htp huq hup
  · by_cases hab : a = b
    · subst b
      have hxy : x ≠ y := by
        intro hxy
        apply hpq
        simp [hxy]
      exact mFiveSameGroup_pair_covered_at_most_once L a x y hxy t u htp htq hup huq
    · by_cases hthird : (L.matching 2).perm a = b
      · exact mFiveThirdMatching_pair_covered_at_most_once L a b x y hab hthird t u htp htq hup huq
      · by_cases hfirst : (L.matching 0).perm a = b
        · apply mFiveFirstSecondMatching_pair_covered_at_most_once L 0 a b x y hab _ t u htp htq hup huq
          simpa [mFiveFirstSecondMatching] using hfirst
        · by_cases hsecond : (L.matching 1).perm a = b
          · apply mFiveFirstSecondMatching_pair_covered_at_most_once L 1 a b x y hab _ t u htp htq hup huq
            simpa [mFiveFirstSecondMatching] using hsecond
          · apply mFiveNonmatching_pair_covered_at_most_once L a b x y hab _ t u htp htq hup huq
            intro k
            fin_cases k
            · simpa [mFiveFirstSecondMatching] using hfirst
            · simpa [mFiveFirstSecondMatching] using hsecond
            · exact hthird

/-- Feder--Subi's literal `m ≡ 5 (mod 6)` triangle packing above a macro
packing with three matching leaves. -/
private noncomputable def mFivePacking
    (L : TrianglePacking.WithThreeMatchingLeaves α) : TrianglePacking (Fin 5 ⊕ (α × ZMod 3)) where
  Triangle := MFiveTriangleIndex L
  instFintypeTriangle := inferInstance
  instDecidableEqTriangle := by classical exact Classical.decEq _
  vertex := mFiveVertex L
  vertex_injective := mFiveVertex_injective L
  pair_covered_at_most_once := mFivePacking_pair_covered_at_most_once L

private theorem mFivePacking_covers_residual_pair_iff
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r s : Fin 5) (hrs : r ≠ s) :
    (mFivePacking L).CoversPair (Sum.inl r) (Sum.inl s) ↔ finFive.CoversPair r s := by
  constructor
  · rintro ⟨t, hr, hs⟩
    rcases mFiveTriangle_eq_residual_of_covers_two_residual L r s hrs t hr hs with
      ⟨p, hp, hpr, hps⟩
    exact ⟨p, hpr, hps⟩
  · rintro ⟨p, hr, hs⟩
    rcases hr with ⟨i, hi⟩
    rcases hs with ⟨j, hj⟩
    exact ⟨Sum.inl p, ⟨i, congrArg Sum.inl hi⟩, ⟨j, congrArg Sum.inl hj⟩⟩

private theorem mFivePacking_covers_residual_group
    (L : TrianglePacking.WithThreeMatchingLeaves α) (r : Fin 5) (a : α) (x : ZMod 3) :
    (mFivePacking L).CoversPair (Sum.inl r) (Sum.inr (a, x)) := by
  fin_cases r
  · refine ⟨mFiveThirdFactorTriangle L 0 a x, ⟨0, ?_⟩,
      mFiveThirdFactorTriangle_group_vertex L 0 a x⟩
    simpa [mFivePacking, mFiveThirdResidual] using mFiveThirdFactorTriangle_residual_vertex L 0 a x
  · refine ⟨mFiveThirdFactorTriangle L 1 a x, ⟨0, ?_⟩,
      mFiveThirdFactorTriangle_group_vertex L 1 a x⟩
    simpa [mFivePacking, mFiveThirdResidual] using mFiveThirdFactorTriangle_residual_vertex L 1 a x
  · refine ⟨mFiveThirdFactorTriangle L 2 a x, ⟨0, ?_⟩,
      mFiveThirdFactorTriangle_group_vertex L 2 a x⟩
    simpa [mFivePacking, mFiveThirdResidual] using mFiveThirdFactorTriangle_residual_vertex L 2 a x
  · refine ⟨mFiveFirstSecondFactorTriangle L 0 a x, ⟨0, ?_⟩,
      mFiveFirstSecondFactorTriangle_group_vertex L 0 a x⟩
    simpa [mFivePacking, mFiveFirstSecondResidual] using
      mFiveFirstSecondFactorTriangle_residual_vertex L 0 a x
  · refine ⟨mFiveFirstSecondFactorTriangle L 1 a x, ⟨0, ?_⟩,
      mFiveFirstSecondFactorTriangle_group_vertex L 1 a x⟩
    simpa [mFivePacking, mFiveFirstSecondResidual] using
      mFiveFirstSecondFactorTriangle_residual_vertex L 1 a x

private theorem mFivePacking_covers_same_group_pair
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a : α) (x y : ZMod 3) (hxy : x ≠ y) :
    (mFivePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (a, y)) := by
  rcases zModThree_eq_self_or_add_one_or_add_two x y with h | h | h
  · exact False.elim (hxy h.symm)
  · have hback : y + 2 = x := by
      calc
        y + 2 = (x + 1) + 2 := by rw [h]
        _ = x := by
          rw [add_assoc, show (1 + 2 : ZMod 3) = 0 by decide, add_zero]
    refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨a, y⟩))), ⟨2, ?_⟩, ⟨0, ?_⟩⟩
    · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, hback]
    · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex]
  · refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨a, x⟩))), ⟨0, ?_⟩, ⟨2, ?_⟩⟩
    · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex]
    · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, h]

private theorem mFivePacking_covers_nonmatching_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hnonmatching : ∀ r : Fin 3, (L.matching r).perm a ≠ b) :
    (mFivePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  rcases (L.coversPair_iff a b hab).mpr hnonmatching with ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
  have hij : i ≠ j := by
    intro hij
    apply hab
    calc
      a = L.packing.vertex t i := hi.symm
      _ = L.packing.vertex t j := by rw [hij]
      _ = b := hj
  rcases existsUnique_triplingCross_of_distinct i j x y hij with ⟨p, hp, hpuniq⟩
  rcases hp with ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hki : k = i := triplingCrossVertex_index_eq_fst hk
  have hlj : l = j := triplingCrossVertex_index_eq_fst hl
  subst k
  subst l
  refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, p)))), ⟨i, ?_⟩, ⟨j, ?_⟩⟩
  · change Sum.inr (L.packing.vertex t i, (triplingCrossVertex p i).2) = Sum.inr (a, x)
    apply congrArg Sum.inr
    have hoffset : (triplingCrossVertex p i).2 = x := congrArg Prod.snd hk
    rw [hi, hoffset]
  · change Sum.inr (L.packing.vertex t j, (triplingCrossVertex p j).2) = Sum.inr (b, y)
    apply congrArg Sum.inr
    have hoffset : (triplingCrossVertex p j).2 = y := congrArg Prod.snd hl
    rw [hj, hoffset]

private theorem mFivePacking_covers_third_matching_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (a b : α) (x y : ZMod 3)
    (hab : a ≠ b) (hmatching : (L.matching 2).perm a = b) :
    (mFivePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  let M := L.matching 2
  let u := matchingRepresentative M a
  rcases matchingRepresentative_endpoints M a with ha | ha
  · have hua : u.1 = a := by simpa [M, u] using ha.symm
    let r := zModThreeToFin (y - x)
    refine ⟨mFiveThirdFactorTriangle L r a x,
      mFiveThirdFactorTriangle_group_vertex L r a x, ⟨2, ?_⟩⟩
    have hr : (r.1 : ZMod 3) = y - x := by
      exact zModThreeToFin_cast _
    have hraw : (matchingRepresentative (L.matching 2) a).1 = a := by
      simpa [M, u] using hua
    change Sum.inr ((L.matching 2).perm (matchingRepresentative (L.matching 2) a).1,
      (if a = (matchingRepresentative (L.matching 2) a).1 then x else x - (r.1 : ZMod 3)) +
        (r.1 : ZMod 3)) = Sum.inr (b, y)
    rw [if_pos hraw.symm, hraw, hmatching]
    congr 2
    calc
      x + (r.1 : ZMod 3) = x + (y - x) := by rw [hr]
      _ = y := by ring
  · have hMa : M.perm u.1 = a := by simpa [M, u] using ha.symm
    have hub : u.1 = b := by
      calc
        u.1 = M.perm (M.perm u.1) := (M.apply_apply u.1).symm
        _ = M.perm a := by rw [hMa]
        _ = b := hmatching
    have hne : a ≠ u.1 := by
      intro h
      apply hab
      calc
        a = u.1 := h
        _ = b := hub
    let r := zModThreeToFin (x - y)
    refine ⟨mFiveThirdFactorTriangle L r a x,
      mFiveThirdFactorTriangle_group_vertex L r a x, ⟨1, ?_⟩⟩
    have hr : (r.1 : ZMod 3) = x - y := by
      exact zModThreeToFin_cast _
    have hraw : (matchingRepresentative (L.matching 2) a).1 = b := by
      simpa [M, u] using hub
    have hrawne : a ≠ (matchingRepresentative (L.matching 2) a).1 := by
      simpa [M, u] using hne
    change Sum.inr ((matchingRepresentative (L.matching 2) a).1,
      if a = (matchingRepresentative (L.matching 2) a).1 then x else x - (r.1 : ZMod 3)) =
        Sum.inr (b, y)
    rw [if_neg hrawne, hraw]
    congr 2
    calc
      x - (r.1 : ZMod 3) = x - (x - y) := by rw [hr]
      _ = y := by ring

private theorem mFivePacking_covers_firstSecond_factor_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a b : α) (x : ZMod 3)
    (hmatching : (L.matching (mFiveFirstSecondMatching k)).perm a = b) :
    (mFivePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, x)) := by
  let M := L.matching (mFiveFirstSecondMatching k)
  let u := matchingRepresentative M a
  rcases matchingRepresentative_endpoints M a with ha | ha
  · have hua : u.1 = a := by simpa [M, u] using ha.symm
    refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨k, u, x⟩)), ⟨1, ?_⟩, ⟨2, ?_⟩⟩
    · simp [mFivePacking, mFiveVertex, hua]
    · simp [mFivePacking, mFiveVertex, hua, hmatching]
  · have hMa : M.perm u.1 = a := by simpa [M, u] using ha.symm
    have hLMa : (L.matching (mFiveFirstSecondMatching k)).perm u.1 = a := by
      simpa [M] using hMa
    have hub : u.1 = b := by
      calc
        u.1 = M.perm (M.perm u.1) := (M.apply_apply u.1).symm
        _ = M.perm a := by rw [hMa]
        _ = b := hmatching
    refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨k, u, x⟩)), ⟨2, ?_⟩, ⟨1, ?_⟩⟩
    · simp [mFivePacking, mFiveVertex, hLMa]
    · simp [mFivePacking, mFiveVertex, hub]

private theorem mFivePacking_covers_firstSecond_fill_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a b : α)
    (x y : ZMod 3) (hxy : x ≠ y)
    (hmatching : (L.matching (mFiveFirstSecondMatching k)).perm a = b) :
    (mFivePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  rcases mFiveFirstSecond_edge_oriented L k a b hmatching with hor | hor
  · rcases zModThree_eq_self_or_add_one_or_add_two x y with h | h | h
    · exact False.elim (hxy h.symm)
    · refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨a, x⟩))), ⟨0, ?_⟩, ⟨1, ?_⟩⟩
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex]
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, hor, h]
    · have hax : y - 1 + 2 = x := by
        calc
          y - 1 + 2 = y + 1 := by ring
          _ = (x + 2) + 1 := by rw [h]
          _ = x := by
            rw [add_assoc, show (2 + 1 : ZMod 3) = 0 by decide, add_zero]
      refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨a, y - 1⟩))), ⟨2, ?_⟩, ⟨1, ?_⟩⟩
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, hax]
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, hor]
  · rcases zModThree_eq_self_or_add_one_or_add_two x y with h | h | h
    · exact False.elim (hxy h.symm)
    · have hby : x - 1 + 2 = y := by
        calc
          x - 1 + 2 = x + 1 := by ring
          _ = y := h.symm
      refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨b, x - 1⟩))), ⟨1, ?_⟩, ⟨2, ?_⟩⟩
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, hor]
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, hby]
    · have hay : y + 1 = x := by
        calc
          y + 1 = (x + 2) + 1 := by rw [h]
          _ = x := by
            rw [add_assoc, show (2 + 1 : ZMod 3) = 0 by decide, add_zero]
      refine ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨b, y⟩))), ⟨1, ?_⟩, ⟨0, ?_⟩⟩
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex, hor, hay]
      · simp [mFivePacking, mFiveVertex, threeMatchingLeaveMacroVertex]

private theorem mFivePacking_covers_firstSecond_matching_groups
    (L : TrianglePacking.WithThreeMatchingLeaves α) (k : Fin 2) (a b : α)
    (x y : ZMod 3) (hab : a ≠ b)
    (hmatching : (L.matching (mFiveFirstSecondMatching k)).perm a = b) :
    (mFivePacking L).CoversPair (Sum.inr (a, x)) (Sum.inr (b, y)) := by
  by_cases hxy : x = y
  · subst y
    exact mFivePacking_covers_firstSecond_factor_groups L k a b x hmatching
  · exact mFivePacking_covers_firstSecond_fill_groups L k a b x y hxy hmatching

private def mFiveLeaveVertex (i : Fin 4) : Fin 5 ⊕ (α × ZMod 3) :=
  Sum.inl (finFiveLeaveVertex i)

private theorem mFiveLeave_cycle_iff (r s : Fin 5) :
    (∃ i : Fin 4, s(Sum.inl r, Sum.inl s) =
      s(mFiveLeaveVertex (α := α) i, mFiveLeaveVertex (α := α) (fourCycleNext i))) ↔
      ∃ i : Fin 4, s(r, s) =
        s(finFiveLeaveVertex i, finFiveLeaveVertex (fourCycleNext i)) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Sym2.map.injective (fun x y h => Sum.inl.inj h)
    simpa only [Sym2.map_mk, mFiveLeaveVertex] using hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa only [Sym2.map_mk, mFiveLeaveVertex] using congrArg (Sym2.map Sum.inl) hi

/-- The five-residual Feder--Subi construction leaves exactly the four-cycle
in its residual `K₅`. -/
private theorem mFivePacking_leavesFourCycle
    (L : TrianglePacking.WithThreeMatchingLeaves α) :
    (mFivePacking L).LeavesFourCycle (mFiveLeaveVertex (α := α)) := by
  constructor
  · intro i j hij
    apply finFive_leavesFourCycle.1
    exact Sum.inl.inj hij
  · rintro (r | ⟨a, x⟩) (s | ⟨b, y⟩) hxy
    · have hrs : r ≠ s := by
        intro hrs
        apply hxy
        rw [hrs]
      constructor
      · intro hcover
        have hbase : finFive.CoversPair r s :=
          (mFivePacking_covers_residual_pair_iff L r s hrs).mp hcover
        have hnotbase : ¬ ∃ i : Fin 4, s(r, s) =
            s(finFiveLeaveVertex i, finFiveLeaveVertex (fourCycleNext i)) :=
          (finFive_leavesFourCycle.2 r s hrs).mp hbase
        intro hcycle
        apply hnotbase
        exact (mFiveLeave_cycle_iff (α := α) r s).mp hcycle
      · intro hnotcycle
        apply (mFivePacking_covers_residual_pair_iff L r s hrs).mpr
        apply (finFive_leavesFourCycle.2 r s hrs).mpr
        intro hbasecycle
        apply hnotcycle
        exact (mFiveLeave_cycle_iff (α := α) r s).mpr hbasecycle
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨_, hright⟩ | ⟨_, hright⟩
        · simp [mFiveLeaveVertex] at hright
        · simp [mFiveLeaveVertex] at hright
      · intro hnotcycle
        exact mFivePacking_covers_residual_group L r b y
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [mFiveLeaveVertex] at hleft
        · simp [mFiveLeaveVertex] at hleft
      · intro hnotcycle
        rcases mFivePacking_covers_residual_group L s a x with ⟨t, hs, ha⟩
        exact ⟨t, ha, hs⟩
    · constructor
      · intro hcover hcycle
        rcases hcycle with ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨hleft, _⟩ | ⟨hleft, _⟩
        · simp [mFiveLeaveVertex] at hleft
        · simp [mFiveLeaveVertex] at hleft
      · intro hnotcycle
        by_cases hab : a = b
        · subst b
          have hxy' : x ≠ y := by
            intro hxy'
            apply hxy
            simp [hxy']
          exact mFivePacking_covers_same_group_pair L a x y hxy'
        · by_cases hthird : (L.matching 2).perm a = b
          · exact mFivePacking_covers_third_matching_groups L a b x y hab hthird
          · by_cases hfirst : (L.matching 0).perm a = b
            · apply mFivePacking_covers_firstSecond_matching_groups L 0 a b x y hab
              simpa [mFiveFirstSecondMatching] using hfirst
            · by_cases hsecond : (L.matching 1).perm a = b
              · apply mFivePacking_covers_firstSecond_matching_groups L 1 a b x y hab
                simpa [mFiveFirstSecondMatching] using hsecond
              · apply mFivePacking_covers_nonmatching_groups L a b x y hab
                intro k
                fin_cases k
                · simpa [mFiveFirstSecondMatching] using hfirst
                · simpa [mFiveFirstSecondMatching] using hsecond
                · exact hthird

private theorem card_mFiveCarrier (n : ℕ) :
    Fintype.card (Fin 5 ⊕ (Fin n × ZMod 3)) = 3 * n + 5 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  omega

/-- Finite-label form of the final three-matching-leave macro expansion. -/
private noncomputable def mFivePackingFin
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :
    TrianglePacking (Fin (3 * n + 5)) := by
  let e : Fin 5 ⊕ (Fin n × ZMod 3) ≃ Fin (3 * n + 5) :=
    Fintype.equivFinOfCardEq (card_mFiveCarrier n)
  exact (mFivePacking (tripleRemovedWithThreeMatchingLeavesFin S T)).map e

/-- Feder--Subi's final three-matching-leave case: deleting one triple from
an `STS(n+3)` and expanding every remaining point to a three-point fibre
produces a finite packing with exactly one four-cycle leave. -/
theorem exists_threeMatchingLeavePackingFin_leavesFourCycle
    (S : SteinerTripleSystem (Fin (n + 3))) (T : S.Triangle) :
    ∃ v : Fin 4 → Fin (3 * n + 5),
      (mFivePackingFin S T).LeavesFourCycle v := by
  let e : Fin 5 ⊕ (Fin n × ZMod 3) ≃ Fin (3 * n + 5) :=
    Fintype.equivFinOfCardEq (card_mFiveCarrier n)
  refine ⟨e ∘ mFiveLeaveVertex, ?_⟩
  exact TrianglePacking.map_leavesFourCycle e
    (mFivePacking (tripleRemovedWithThreeMatchingLeavesFin S T)) mFiveLeaveVertex
    (mFivePacking_leavesFourCycle (tripleRemovedWithThreeMatchingLeavesFin S T))

/-- Feder--Subi's final `m ≡ 5 (mod 6)` subcase.  Its macro system has
order `2m+3 ≡ 1 (mod 6)`; deleting one of its triples and applying the
three-matching expansion gives a packing on `6m+5` points with one
four-cycle leave. -/
theorem exists_threeMatchingLeavePackingFin_leavesFourCycle_of_modSix
    (m : ℕ) (hm : m % 6 = 5) :
    ∃ (P : TrianglePacking (Fin (6 * m + 5))) (v : Fin 4 → Fin (6 * m + 5)),
      P.LeavesFourCycle v := by
  let S : SteinerTripleSystem (Fin (2 * m + 3)) :=
    (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (2 * m + 3) (by
      left
      omega)).some
  have hm_lower : 5 ≤ m := by
    calc
      5 = m % 6 := hm.symm
      _ ≤ m := Nat.mod_le _ _
  let T : S.Triangle := S.triangleOfPair
    ⟨0, by omega⟩ ⟨1, by omega⟩ (by
      intro h
      have hval := congrArg Fin.val h
      norm_num at hval)
  have hsize : 3 * (2 * m) + 5 = 6 * m + 5 := by omega
  let e : Fin (3 * (2 * m) + 5) ≃ Fin (6 * m + 5) :=
    (Fin.castOrderIso hsize).toEquiv
  let P : TrianglePacking (Fin (6 * m + 5)) := by
    exact (mFivePackingFin (n := 2 * m) S T).map e
  refine ⟨P, ?_⟩
  obtain ⟨v, hv⟩ :=
    exists_threeMatchingLeavePackingFin_leavesFourCycle (n := 2 * m) S T
  exact ⟨e ∘ v, TrianglePacking.map_leavesFourCycle e
    (mFivePackingFin (n := 2 * m) S T) v hv⟩

/-- Feder--Subi's finite construction of a triangle packing with a single
four-cycle leave on `6m+5` points.  The six cases use the source's group-six,
dense-split, three-point-group, and three-matching expansions respectively. -/
theorem exists_federSubiPackingFin_leavesFourCycle (m : ℕ) :
    ∃ (P : TrianglePacking (Fin (6 * m + 5))) (v : Fin 4 → Fin (6 * m + 5)),
      P.LeavesFourCycle v := by
  have hmod : m % 6 < 6 := Nat.mod_lt _ (by omega)
  interval_cases h : m % 6
  · let S : SteinerTripleSystem (Fin (m + 1)) :=
      (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (m + 1) (by
        left
        omega)).some
    refine ⟨matchingLeavePackingFin S, ?_⟩
    simpa only [S] using
      exists_matchingLeavePackingFin_leavesFourCycle_of_modSix m (Or.inl h)
  · let S : SteinerTripleSystem (Fin m) :=
      (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix m (by
        left
        omega)).some
    refine ⟨sixGroupPackingFin S, ?_⟩
    exact exists_sixGroupPackingFin_leavesFourCycle S
  · let S : SteinerTripleSystem (Fin (m + 1)) :=
      (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (m + 1) (by
        right
        omega)).some
    refine ⟨matchingLeavePackingFin S, ?_⟩
    simpa only [S] using
      exists_matchingLeavePackingFin_leavesFourCycle_of_modSix m (Or.inr h)
  · let S : SteinerTripleSystem (Fin m) :=
      (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix m (by
        right
        omega)).some
    refine ⟨sixGroupPackingFin S, ?_⟩
    exact exists_sixGroupPackingFin_leavesFourCycle S
  · let S : SteinerTripleSystem (Fin (2 * m + 1)) :=
      (SteinerTripleSystem.steinerTripleSystem_exists_of_modSix (2 * m + 1) (by
        right
        omega)).some
    refine ⟨threePointMatchingLeavePackingFin S, ?_⟩
    simpa only [S] using
      exists_threePointMatchingLeavePackingFin_leavesFourCycle_of_modSix m h
  · exact exists_threeMatchingLeavePackingFin_leavesFourCycle_of_modSix m h

end ThreeMatchingLeaveMacro

end ThreePointMatchingBlocks

end KirkmanSixGroups

end TrianglePacking

end Combinatorics
end Foundations
end AppliedModelingLib
