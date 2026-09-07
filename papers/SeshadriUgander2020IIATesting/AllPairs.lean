import SeshadriUgander2020IIATesting.SingleBigCycle
import AppliedModelingLib.Foundations.Combinatorics.SteinerTriple
import AppliedModelingLib.Foundations.Combinatorics.SteinerTripleConstructions

/-!
# The all-pairs comparison frame

This is the second special comparison family in Section 7 of
Seshadri--Ugander (2020).  A choice set is an unordered pair of items.  The
source obtains six-cycles by decomposing the complete graph into triangles;
the general triangle-design interface lives in
`AppliedModelingLib.Foundations.Combinatorics.SteinerTriple`.
-/

namespace SeshadriUgander2020IIATesting

namespace AllPairs

/-- The two-item choice sets on `Fin n`. -/
abbrev ChoiceSet (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

/-- The all-pairs choice frame, defined for at least two items. -/
noncomputable def frame (n : ℕ) (hn : 2 ≤ n) : ChoiceFrame where
  Item := Fin n
  instFintypeItem := inferInstance
  instDecidableEqItem := inferInstance
  SetId := ChoiceSet n
  instFintypeSetId := inferInstance
  instDecidableEqSetId := inferInstance
  members C := C.1
  nonempty_sets := by
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    refine ⟨⟨{a, b}, ?_⟩⟩
    have hab : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      simp [a, b] at this
    simp [hab]
  card_two_le C := by omega

@[simp] theorem members_card (n : ℕ) (hn : 2 ≤ n) (C : (frame n hn).SetId) :
    ((frame n hn).members C).card = 2 := C.2

@[simp] theorem frame_itemCard (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (frame n hn).Item = n := by
  exact Fintype.card_fin n

/-- Package a pair of distinct items as a choice-set index. -/
def pair (n : ℕ) {x y : Fin n} (hxy : x ≠ y) : ChoiceSet n :=
  ⟨{x, y}, by simp [hxy]⟩

@[simp] theorem mem_pair_left (n : ℕ) {x y : Fin n} (hxy : x ≠ y) :
    x ∈ (pair n hxy : Finset (Fin n)) := by
  simp [pair]

@[simp] theorem mem_pair_right (n : ℕ) {x y : Fin n} (hxy : x ≠ y) :
    y ∈ (pair n hxy : Finset (Fin n)) := by
  simp [pair]

@[simp] theorem pair_eq_pair_iff {n : ℕ} {x y u v : Fin n}
    (hxy : x ≠ y) (huv : u ≠ v) :
    pair n hxy = pair n huv ↔ ({x, y} : Finset (Fin n)) = {u, v} := by
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

private def cycleEdge (e : Fin 6) : Fin 3 :=
  ⟨e.1 / 2, by omega⟩

private def cycleEndpoint (e : Fin 6) : Fin 3 :=
  if e = 0 then 0
  else if e = 1 then 1
  else if e = 2 then 1
  else if e = 3 then 2
  else if e = 4 then 2
  else 0

private theorem cycleEdge_endpoint_injective :
    Function.Injective (fun e : Fin 6 => (cycleEdge e, cycleEndpoint e)) := by
  intro e f h
  fin_cases e <;> fin_cases f <;> simp [cycleEdge, cycleEndpoint] at h ⊢

section TriangleBridge

variable {n : ℕ} (hn : 2 ≤ n)
variable (S : AppliedModelingLib.Foundations.Combinatorics.SteinerTripleSystem (Fin n))

private noncomputable abbrev F := frame n hn

private def triangleVertex (t : S.Triangle) (i : Fin 3) : Fin n := S.vertex t i

private theorem triangleVertex_ne {t : S.Triangle} {i j : Fin 3} (hij : i ≠ j) :
    triangleVertex S t i ≠ triangleVertex S t j :=
  S.vertex_ne_of_ne hij

private noncomputable def cycleObservation (t : S.Triangle) (e : Fin 6) : (F hn).Observation :=
  if e = 0 then
    ⟨pair n (triangleVertex_ne S (t := t) (show (0 : Fin 3) ≠ 1 by decide)),
      ⟨triangleVertex S t 0, mem_pair_left n (triangleVertex_ne S (t := t) (by decide))⟩⟩
  else if e = 1 then
    ⟨pair n (triangleVertex_ne S (t := t) (show (0 : Fin 3) ≠ 1 by decide)),
      ⟨triangleVertex S t 1, mem_pair_right n (triangleVertex_ne S (t := t) (by decide))⟩⟩
  else if e = 2 then
    ⟨pair n (triangleVertex_ne S (t := t) (show (1 : Fin 3) ≠ 2 by decide)),
      ⟨triangleVertex S t 1, mem_pair_left n (triangleVertex_ne S (t := t) (by decide))⟩⟩
  else if e = 3 then
    ⟨pair n (triangleVertex_ne S (t := t) (show (1 : Fin 3) ≠ 2 by decide)),
      ⟨triangleVertex S t 2, mem_pair_right n (triangleVertex_ne S (t := t) (by decide))⟩⟩
  else if e = 4 then
    ⟨pair n (triangleVertex_ne S (t := t) (show (2 : Fin 3) ≠ 0 by decide)),
      ⟨triangleVertex S t 2, mem_pair_left n (triangleVertex_ne S (t := t) (by decide))⟩⟩
  else
    ⟨pair n (triangleVertex_ne S (t := t) (show (2 : Fin 3) ≠ 0 by decide)),
      ⟨triangleVertex S t 0, mem_pair_right n (triangleVertex_ne S (t := t) (by decide))⟩⟩

private def edgeChoice (t : S.Triangle) (i : Fin 3) : ChoiceSet n :=
  if i = 0 then
    pair n (triangleVertex_ne S (t := t) (show (0 : Fin 3) ≠ 1 by decide))
  else if i = 1 then
    pair n (triangleVertex_ne S (t := t) (show (1 : Fin 3) ≠ 2 by decide))
  else
    pair n (triangleVertex_ne S (t := t) (show (2 : Fin 3) ≠ 0 by decide))

/-- The non-closing five-edge path in the incidence six-cycle induced by one
ordered Steiner triple. -/
private noncomputable def triangleCycleTail (t : S.Triangle) :
    (F hn).incidenceGraph.Walk (Sum.inl (triangleVertex S t 1))
      (Sum.inr (edgeChoice S t 0)) :=
  SimpleGraph.Walk.cons' (Sum.inl (triangleVertex S t 1)) (Sum.inr (edgeChoice S t 1))
    (Sum.inr (edgeChoice S t 0)) (by
    change triangleVertex S t 1 ∈ (F hn).members (edgeChoice S t 1)
    change triangleVertex S t 1 ∈
      ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n))
    simp)
  (SimpleGraph.Walk.cons' (Sum.inr (edgeChoice S t 1)) (Sum.inl (triangleVertex S t 2))
    (Sum.inr (edgeChoice S t 0)) (by
    change triangleVertex S t 2 ∈ (F hn).members (edgeChoice S t 1)
    change triangleVertex S t 2 ∈
      ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n))
    simp)
  (SimpleGraph.Walk.cons' (Sum.inl (triangleVertex S t 2)) (Sum.inr (edgeChoice S t 2))
    (Sum.inr (edgeChoice S t 0)) (by
    change triangleVertex S t 2 ∈ (F hn).members (edgeChoice S t 2)
    change triangleVertex S t 2 ∈
      ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n))
    simp)
  (SimpleGraph.Walk.cons' (Sum.inr (edgeChoice S t 2)) (Sum.inl (triangleVertex S t 0))
    (Sum.inr (edgeChoice S t 0)) (by
    change triangleVertex S t 0 ∈ (F hn).members (edgeChoice S t 2)
    change triangleVertex S t 0 ∈
      ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n))
    simp)
  (SimpleGraph.Walk.cons' (Sum.inl (triangleVertex S t 0)) (Sum.inr (edgeChoice S t 0))
    (Sum.inr (edgeChoice S t 0)) (by
    change triangleVertex S t 0 ∈ (F hn).members (edgeChoice S t 0)
    change triangleVertex S t 0 ∈
      ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n))
    simp)
  SimpleGraph.Walk.nil))))

/-- The literal incidence-graph six-cycle induced by one ordered Steiner
triple.  Its successive vertices are the three pair-choice nodes and the
three item nodes in cyclic order. -/
private noncomputable def triangleCycleWalk (t : S.Triangle) :
    (F hn).incidenceGraph.Walk (Sum.inr (edgeChoice S t 0))
      (Sum.inr (edgeChoice S t 0)) :=
  SimpleGraph.Walk.cons' (Sum.inr (edgeChoice S t 0)) (Sum.inl (triangleVertex S t 1))
    (Sum.inr (edgeChoice S t 0)) (by
    change triangleVertex S t 1 ∈ (F hn).members (edgeChoice S t 0)
    change triangleVertex S t 1 ∈
      ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n))
    simp)
  (triangleCycleTail hn S t)

private theorem cycleObservation_choice_eq_edgeChoice (t : S.Triangle) (e : Fin 6) :
    (cycleObservation hn S t e).1 = edgeChoice S t (cycleEdge e) := by
  fin_cases e <;> rfl

private theorem cycleObservation_item_eq_triangleVertex (t : S.Triangle) (e : Fin 6) :
    (cycleObservation hn S t e).2.1 = triangleVertex S t (cycleEndpoint e) := by
  fin_cases e <;> rfl

private theorem edgeChoice_injective (t : S.Triangle) :
    Function.Injective (edgeChoice S t) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals exfalso
  all_goals have hset := congrArg Subtype.val hij
  · change ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) =
        {triangleVertex S t 1, triangleVertex S t 2} at hset
    have hmem : triangleVertex S t 0 ∈
        ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact triangleVertex_ne S (t := t) (by decide) h
    · exact triangleVertex_ne S (t := t) (by decide) h
  · change ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) =
        {triangleVertex S t 2, triangleVertex S t 0} at hset
    have hmem : triangleVertex S t 1 ∈
        ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact triangleVertex_ne S (t := t) (by decide) h
    · exact triangleVertex_ne S (t := t) (by decide) h.symm
  · change ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) =
        {triangleVertex S t 0, triangleVertex S t 1} at hset
    have hmem : triangleVertex S t 2 ∈
        ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact triangleVertex_ne S (t := t) (by decide) h
    · exact triangleVertex_ne S (t := t) (by decide) h
  · change ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) =
        {triangleVertex S t 2, triangleVertex S t 0} at hset
    have hmem : triangleVertex S t 1 ∈
        ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact triangleVertex_ne S (t := t) (by decide) h
    · exact triangleVertex_ne S (t := t) (by decide) h.symm
  · change ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) =
        {triangleVertex S t 0, triangleVertex S t 1} at hset
    have hmem : triangleVertex S t 2 ∈
        ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact triangleVertex_ne S (t := t) (by decide) h
    · exact triangleVertex_ne S (t := t) (by decide) h
  · change ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) =
        {triangleVertex S t 1, triangleVertex S t 2} at hset
    have hmem : triangleVertex S t 0 ∈
        ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact triangleVertex_ne S (t := t) (by decide) h
    · exact triangleVertex_ne S (t := t) (by decide) h

private theorem triangleCycleTail_isPath (t : S.Triangle) :
    (triangleCycleTail hn S t).IsPath := by
  have h01 : edgeChoice S t 0 ≠ edgeChoice S t 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (edgeChoice_injective S t h)
  have h02 : edgeChoice S t 0 ≠ edgeChoice S t 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (edgeChoice_injective S t h)
  have h12 : edgeChoice S t 1 ≠ edgeChoice S t 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (edgeChoice_injective S t h)
  rw [SimpleGraph.Walk.isPath_def]
  change [Sum.inl (triangleVertex S t 1), Sum.inr (edgeChoice S t 1),
    Sum.inl (triangleVertex S t 2), Sum.inr (edgeChoice S t 2),
    Sum.inl (triangleVertex S t 0), Sum.inr (edgeChoice S t 0)].Nodup
  have h10 : edgeChoice S t 1 ≠ edgeChoice S t 0 := Ne.symm h01
  have h20 : edgeChoice S t 2 ≠ edgeChoice S t 0 := Ne.symm h02
  have hv01 := triangleVertex_ne S (t := t) (show (0 : Fin 3) ≠ 1 by decide)
  have hv02 := triangleVertex_ne S (t := t) (show (0 : Fin 3) ≠ 2 by decide)
  have hv12 := triangleVertex_ne S (t := t) (show (1 : Fin 3) ≠ 2 by decide)
  have hv10 : triangleVertex S t 1 ≠ triangleVertex S t 0 := Ne.symm hv01
  have hv20 : triangleVertex S t 2 ≠ triangleVertex S t 0 := Ne.symm hv02
  simp [h12, h10, h20, hv12, hv10, hv20]

private theorem triangleCycleWalk_isCycle (t : S.Triangle) :
    (triangleCycleWalk hn S t).IsCycle := by
  unfold triangleCycleWalk
  change (SimpleGraph.Walk.cons _ (triangleCycleTail hn S t)).IsCycle
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨triangleCycleTail_isPath hn S t, ?_⟩
  change s(Sum.inr (edgeChoice S t 0), Sum.inl (triangleVertex S t 1)) ∉
    [s(Sum.inl (triangleVertex S t 1), Sum.inr (edgeChoice S t 1)),
      s(Sum.inr (edgeChoice S t 1), Sum.inl (triangleVertex S t 2)),
      s(Sum.inl (triangleVertex S t 2), Sum.inr (edgeChoice S t 2)),
      s(Sum.inr (edgeChoice S t 2), Sum.inl (triangleVertex S t 0)),
      s(Sum.inl (triangleVertex S t 0), Sum.inr (edgeChoice S t 0))]
  have h01 : edgeChoice S t 0 ≠ edgeChoice S t 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (edgeChoice_injective S t h)
  have h02 : edgeChoice S t 0 ≠ edgeChoice S t 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (edgeChoice_injective S t h)
  have hv01 := triangleVertex_ne S (t := t) (show (0 : Fin 3) ≠ 1 by decide)
  have hv12 := triangleVertex_ne S (t := t) (show (1 : Fin 3) ≠ 2 by decide)
  have hv10 : triangleVertex S t 1 ≠ triangleVertex S t 0 := Ne.symm hv01
  simp [h01, h02, hv12, hv10]

private theorem mem_edgeChoice_mem_support (t : S.Triangle) (i : Fin 3)
    (x : Fin n) (hx : x ∈ (F hn).members (edgeChoice S t i)) :
    x ∈ S.support t := by
  fin_cases i
  · change x ∈ ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · simpa [hx] using S.vertex_mem_support t 0
    · simpa [hx] using S.vertex_mem_support t 1
  · change x ∈ ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · simpa [hx] using S.vertex_mem_support t 1
    · simpa [hx] using S.vertex_mem_support t 2
  · change x ∈ ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · simpa [hx] using S.vertex_mem_support t 2
    · simpa [hx] using S.vertex_mem_support t 0

/-- Distinct Steiner triples have no pair-choice set in common. -/
private theorem edgeChoice_eq_implies_triangle_eq {t u : S.Triangle}
    (hn : 2 ≤ n) {i j : Fin 3} (h : edgeChoice S t i = edgeChoice S u j) : t = u := by
  fin_cases i
  · let x := triangleVertex S t 0
    let y := triangleVertex S t 1
    have hxy : x ≠ y := triangleVertex_ne S (t := t) (by decide)
    have hx : x ∈ (F hn).members (edgeChoice S t 0) := by
      change triangleVertex S t 0 ∈
        ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n))
      simp
    have hy : y ∈ (F hn).members (edgeChoice S t 0) := by
      change triangleVertex S t 1 ∈
        ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n))
      simp
    have hxU : x ∈ S.support u := mem_edgeChoice_mem_support hn S u j x (by rw [← h]; exact hx)
    have hyU : y ∈ S.support u := mem_edgeChoice_mem_support hn S u j y (by rw [← h]; exact hy)
    have ht := S.eq_triangleOfPair_of_contains x y hxy t ⟨0, rfl⟩ ⟨1, rfl⟩
    have hu := S.eq_triangleOfPair_of_contains x y hxy u
      (S.mem_support_iff u x |>.mp hxU) (S.mem_support_iff u y |>.mp hyU)
    exact ht.trans hu.symm
  · let x := triangleVertex S t 1
    let y := triangleVertex S t 2
    have hxy : x ≠ y := triangleVertex_ne S (t := t) (by decide)
    have hx : x ∈ (F hn).members (edgeChoice S t 1) := by
      change triangleVertex S t 1 ∈
        ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n))
      simp
    have hy : y ∈ (F hn).members (edgeChoice S t 1) := by
      change triangleVertex S t 2 ∈
        ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n))
      simp
    have hxU : x ∈ S.support u := mem_edgeChoice_mem_support hn S u j x (by rw [← h]; exact hx)
    have hyU : y ∈ S.support u := mem_edgeChoice_mem_support hn S u j y (by rw [← h]; exact hy)
    have ht := S.eq_triangleOfPair_of_contains x y hxy t ⟨1, rfl⟩ ⟨2, rfl⟩
    have hu := S.eq_triangleOfPair_of_contains x y hxy u
      (S.mem_support_iff u x |>.mp hxU) (S.mem_support_iff u y |>.mp hyU)
    exact ht.trans hu.symm
  · let x := triangleVertex S t 2
    let y := triangleVertex S t 0
    have hxy : x ≠ y := triangleVertex_ne S (t := t) (by decide)
    have hx : x ∈ (F hn).members (edgeChoice S t 2) := by
      change triangleVertex S t 2 ∈
        ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n))
      simp
    have hy : y ∈ (F hn).members (edgeChoice S t 2) := by
      change triangleVertex S t 0 ∈
        ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n))
      simp
    have hxU : x ∈ S.support u := mem_edgeChoice_mem_support hn S u j x (by rw [← h]; exact hx)
    have hyU : y ∈ S.support u := mem_edgeChoice_mem_support hn S u j y (by rw [← h]; exact hy)
    have ht := S.eq_triangleOfPair_of_contains x y hxy t ⟨2, rfl⟩ ⟨0, rfl⟩
    have hu := S.eq_triangleOfPair_of_contains x y hxy u
      (S.mem_support_iff u x |>.mp hxU) (S.mem_support_iff u y |>.mp hyU)
    exact ht.trans hu.symm

private theorem cycleObservation_injective (t : S.Triangle) :
    Function.Injective (cycleObservation hn S t) := by
  intro e f hef
  have hchoice : (cycleObservation hn S t e).1 = (cycleObservation hn S t f).1 :=
    congrArg Sigma.fst hef
  rw [cycleObservation_choice_eq_edgeChoice, cycleObservation_choice_eq_edgeChoice] at hchoice
  have hedge : cycleEdge e = cycleEdge f := edgeChoice_injective S t hchoice
  have hitem : (cycleObservation hn S t e).2.1 = (cycleObservation hn S t f).2.1 :=
    congrArg (fun o => o.2.1) hef
  have hendpoint : cycleEndpoint e = cycleEndpoint f := by
    apply S.vertex_injective t
    change triangleVertex S t (cycleEndpoint e) = triangleVertex S t (cycleEndpoint f)
    rw [← cycleObservation_item_eq_triangleVertex hn S t e,
      ← cycleObservation_item_eq_triangleVertex hn S t f]
    exact hitem
  exact cycleEdge_endpoint_injective (Prod.ext hedge hendpoint)

private theorem globalCycleObservation_injective :
    Function.Injective (fun p : Sigma fun _ : S.Triangle => Fin 6 =>
      cycleObservation hn S p.1 p.2) := by
  rintro ⟨t, e⟩ ⟨u, f⟩ h
  have hchoice : edgeChoice S t (cycleEdge e) = edgeChoice S u (cycleEdge f) := by
    rw [← cycleObservation_choice_eq_edgeChoice hn S t e,
      ← cycleObservation_choice_eq_edgeChoice hn S u f]
    exact congrArg Sigma.fst h
  have htu : t = u := edgeChoice_eq_implies_triangle_eq S hn hchoice
  subst u
  have hef : e = f := cycleObservation_injective hn S t h
  subst f
  rfl

private theorem cycleObservation_eq_of_choice_and_item
    (t : S.Triangle) (e : Fin 6) (x y : Fin n) (hxy : x ≠ y)
    (hchoice : (F hn).members (cycleObservation hn S t e).1 = {x, y})
    (hitem : (cycleObservation hn S t e).2.1 = x) :
    cycleObservation hn S t e =
      ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ := by
  apply Sigma.ext
  · apply Subtype.ext
    exact hchoice
  · apply (Subtype.heq_iff_coe_eq (fun candidate => by
      change candidate ∈ (F hn).members (cycleObservation hn S t e).1 ↔
        candidate ∈ (pair n hxy : Finset (Fin n))
      rw [hchoice]
      rfl)).mpr
    exact hitem

private theorem exists_cycleObservation_eq_pair (x y : Fin n) (hxy : x ≠ y) :
    ∃ (t : S.Triangle) (e : Fin 6),
      cycleObservation hn S t e =
        ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ := by
  let t := S.triangleOfPair x y hxy
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := S.pair_mem_triangleOfPair x y hxy
  change triangleVertex S t i = x at hi
  change triangleVertex S t j = y at hj
  have hij : i ≠ j := by
    intro h
    apply hxy
    calc
      x = triangleVertex S t i := hi.symm
      _ = triangleVertex S t j := congrArg (triangleVertex S t) h
      _ = y := hj
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change triangleVertex S t 0 = x at hi
    change triangleVertex S t 1 = y at hj
    refine ⟨t, 0, cycleObservation_eq_of_choice_and_item hn S t 0 x y hxy ?_ hi⟩
    change ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) = {x, y}
    rw [hi, hj]
  · change triangleVertex S t 0 = x at hi
    change triangleVertex S t 2 = y at hj
    refine ⟨t, 5, cycleObservation_eq_of_choice_and_item hn S t 5 x y hxy ?_ hi⟩
    change ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) = {x, y}
    rw [hj, hi]
    exact Finset.pair_comm _ _
  · change triangleVertex S t 1 = x at hi
    change triangleVertex S t 0 = y at hj
    refine ⟨t, 1, cycleObservation_eq_of_choice_and_item hn S t 1 x y hxy ?_ hi⟩
    change ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) = {x, y}
    rw [hj, hi]
    exact Finset.pair_comm _ _
  · exact (hij rfl).elim
  · change triangleVertex S t 1 = x at hi
    change triangleVertex S t 2 = y at hj
    refine ⟨t, 2, cycleObservation_eq_of_choice_and_item hn S t 2 x y hxy ?_ hi⟩
    change ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) = {x, y}
    rw [hi, hj]
  · change triangleVertex S t 2 = x at hi
    change triangleVertex S t 0 = y at hj
    refine ⟨t, 4, cycleObservation_eq_of_choice_and_item hn S t 4 x y hxy ?_ hi⟩
    change ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) = {x, y}
    rw [hi, hj]
  · change triangleVertex S t 2 = x at hi
    change triangleVertex S t 1 = y at hj
    refine ⟨t, 3, cycleObservation_eq_of_choice_and_item hn S t 3 x y hxy ?_ hi⟩
    change ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) = {x, y}
    rw [hj, hi]
    exact Finset.pair_comm _ _
  · exact (hij rfl).elim

private theorem pairObservation_eq_of_members
    (C : ChoiceSet n) (x : {z : Fin n // z ∈ (F hn).members C})
    (u v : Fin n) (huv : u ≠ v) (hC : C = pair n huv) (hx : x.1 = u) :
    (⟨pair n huv, ⟨u, mem_pair_left n huv⟩⟩ : (F hn).Observation) = ⟨C, x⟩ := by
  refine Sigma.ext hC.symm ?_
  apply (Subtype.heq_iff_coe_eq (fun candidate => by simp [hC])).mpr
  exact hx.symm

private theorem globalCycleObservation_surjective :
    Function.Surjective (fun p : Sigma fun _ : S.Triangle => Fin 6 =>
      cycleObservation hn S p.1 p.2) := by
  rintro ⟨C, x⟩
  obtain ⟨u, v, huv, hCval⟩ := Finset.card_eq_two.mp C.2
  have hxmem : x.1 ∈ (C.1 : Finset (Fin n)) := x.2
  rw [hCval] at hxmem
  have hC : C = pair n huv := by
    apply Subtype.ext
    simpa [pair] using hCval
  have hxuv : x.1 = u ∨ x.1 = v := by
    change x.1 ∈ insert u ({v} : Finset (Fin n)) at hxmem
    rcases Finset.mem_insert.mp hxmem with hxu | hxv
    · exact Or.inl hxu
    · exact Or.inr (Finset.mem_singleton.mp hxv)
  rcases hxuv with hxu | hxv
  · obtain ⟨t, e, he⟩ := exists_cycleObservation_eq_pair hn S u v huv
    refine ⟨⟨t, e⟩, he.trans ?_⟩
    exact pairObservation_eq_of_members hn C x u v huv hC hxu
  · have hvu : v ≠ u := Ne.symm huv
    have hC' : C = pair n hvu := by
      apply Subtype.ext
      change C.1 = ({v, u} : Finset (Fin n))
      rw [hCval]
      exact Finset.pair_comm _ _
    obtain ⟨t, e, he⟩ := exists_cycleObservation_eq_pair hn S v u hvu
    refine ⟨⟨t, e⟩, he.trans ?_⟩
    exact pairObservation_eq_of_members hn C x v u hvu hC' hxv

private noncomputable def globalCycleObservationEquiv :
    (Sigma fun _ : S.Triangle => Fin 6) ≃ (F hn).Observation :=
  Equiv.ofBijective _ ⟨globalCycleObservation_injective hn S,
    globalCycleObservation_surjective hn S⟩

/-- The observation numbered `e` is the edge immediately preceding its item
endpoint in the displayed six-cycle. -/
private def cycleObservationPosition (e : Fin 6) : Fin 6 :=
  ⟨(e.1 + 5) % 6, Nat.mod_lt _ (by decide)⟩

private def edgePositionObservation (e : Fin 6) : Fin 6 :=
  ⟨(e.1 + 1) % 6, Nat.mod_lt _ (by decide)⟩

private theorem cycleObservationPosition_edgePositionObservation (e : Fin 6) :
    cycleObservationPosition (edgePositionObservation e) = e := by
  fin_cases e <;> rfl

private theorem observationEdge_cycleObservation_eq_edgeAt
    (t : S.Triangle) (e : Fin 6) :
    (F hn).observationEdge (cycleObservation hn S t e) =
      AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (triangleCycleWalk hn S t)
        (cycleObservationPosition e) := by
  fin_cases e
  · rfl
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨rfl, rfl⟩

private noncomputable def trianglePacking :
    AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking (F hn).incidenceGraph 6 where
  Cycle := S.Triangle
  instFintypeCycle := inferInstance
  instDecidableEqCycle := inferInstance
  walk := fun t => ⟨Sum.inr (edgeChoice S t 0), triangleCycleWalk hn S t⟩
  isCycle := fun t => triangleCycleWalk_isCycle hn S t
  length_le := by
    intro t
    change (triangleCycleWalk hn S t).length ≤ 6
    rfl
  pairwiseDisjoint := by
    intro t _ u _ htu
    apply Finset.disjoint_left.2
    intro edge hedget hedgeu
    change edge ∈ (triangleCycleWalk hn S t).edges.toFinset at hedget
    change edge ∈ (triangleCycleWalk hn S u).edges.toFinset at hedgeu
    let positionT : Fin 6 :=
      (AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (triangleCycleWalk_isCycle hn S t)).symm ⟨edge, hedget⟩
    let positionU : Fin 6 :=
      (AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (triangleCycleWalk_isCycle hn S u)).symm ⟨edge, hedgeu⟩
    have hpositionT :
        AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (triangleCycleWalk hn S t)
          positionT = edge := by
      change ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (triangleCycleWalk_isCycle hn S t) positionT).1) = edge
      exact congrArg Subtype.val
        ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
          (triangleCycleWalk_isCycle hn S t)).apply_symm_apply ⟨edge, hedget⟩)
    have hpositionU :
        AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (triangleCycleWalk hn S u)
          positionU = edge := by
      change ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (triangleCycleWalk_isCycle hn S u) positionU).1) = edge
      exact congrArg Subtype.val
        ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
          (triangleCycleWalk_isCycle hn S u)).apply_symm_apply ⟨edge, hedgeu⟩)
    have hobsT :
        (F hn).observationEdge
          (cycleObservation hn S t (edgePositionObservation positionT)) = edge := by
      rw [observationEdge_cycleObservation_eq_edgeAt,
        cycleObservationPosition_edgePositionObservation]
      exact hpositionT
    have hobsU :
        (F hn).observationEdge
          (cycleObservation hn S u (edgePositionObservation positionU)) = edge := by
      rw [observationEdge_cycleObservation_eq_edgeAt,
        cycleObservationPosition_edgePositionObservation]
      exact hpositionU
    have hobs : cycleObservation hn S t (edgePositionObservation positionT) =
        cycleObservation hn S u (edgePositionObservation positionU) :=
      (F hn).observationEdge_injective (hobsT.trans hobsU.symm)
    have htu' : (⟨t, edgePositionObservation positionT⟩ :
        Sigma fun _ : S.Triangle => Fin 6) =
        ⟨u, edgePositionObservation positionU⟩ :=
      globalCycleObservation_injective hn S hobs
    exact htu (congrArg Sigma.fst htu')

private theorem trianglePacking_isComplete : (trianglePacking hn S).IsComplete := by
  unfold AppliedModelingLib.Foundations.Graph.PartialSimpleCyclePacking.IsComplete
  apply Set.Subset.antisymm
  · intro edge hedge
    change edge ∈ (trianglePacking hn S).usedEdges at hedge
    rw [← SimpleGraph.coe_edgeFinset]
    exact (trianglePacking hn S).usedEdges_subset_edgeFinset hedge
  · intro edge hedge
    obtain ⟨o, ho⟩ := (F hn).observationEdge_surjective_edgeSet ⟨edge, hedge⟩
    obtain ⟨⟨t, e⟩, he⟩ := globalCycleObservation_surjective hn S o
    change edge ∈ (trianglePacking hn S).usedEdges
    apply Finset.mem_biUnion.mpr
    refine ⟨t, Finset.mem_univ _, ?_⟩
    change edge ∈ (triangleCycleWalk hn S t).edges.toFinset
    change (F hn).observationEdge o = edge at ho
    rw [← ho, ← he, observationEdge_cycleObservation_eq_edgeAt]
    apply List.mem_toFinset.mpr
    exact List.get_mem _ _

theorem incidenceCount_eq_two_choose (n : ℕ) (hn : 2 ≤ n) :
    (frame n hn).incidenceCount = 2 * n.choose 2 := by
  unfold ChoiceFrame.incidenceCount
  simp_rw [members_card]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  change Fintype.card {s : Finset (Fin n) // s.card = 2} * 2 = 2 * n.choose 2
  rw [Fintype.card_finset_len, Fintype.card_fin]
  ring

theorem incidenceCount_eq_mul_pred (n : ℕ) (hn : 2 ≤ n) :
    (frame n hn).incidenceCount = n * (n - 1) := by
  rw [incidenceCount_eq_two_choose, Nat.choose_two_right, mul_comm 2,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]

/-- A Steiner triple system gives the paper's complete all-pairs incidence
packing by literal six-cycles, and hence a balanced signed decomposition. -/
noncomputable def cycleDecompositionOfSteinerTripleSystem :
    ChoiceSystem.CycleDecomposition (frame n hn) :=
  (F hn).cycleDecompositionOfCompletePacking (trianglePacking hn S)
    (trianglePacking_isComplete hn S)

/-- The graph-cycle traversal supplies the alternating witness required by
the paper's finite testing reduction. -/
noncomputable def cycleDecompositionOfSteinerTripleSystem_alternatingCycleWitness :
    (cycleDecompositionOfSteinerTripleSystem hn S).AlternatingCycleWitness :=
  (F hn).cycleDecompositionOfCompletePacking_alternatingCycleWitness
    (trianglePacking hn S) (trianglePacking_isComplete hn S)

theorem cycleDecompositionOfSteinerTripleSystem_length (t : S.Triangle) :
    (cycleDecompositionOfSteinerTripleSystem hn S).length t = 6 := by
  change ((F hn).cycleDecompositionOfCompletePacking (trianglePacking hn S)
    (trianglePacking_isComplete hn S)).length t = 6
  rw [ChoiceFrame.cycleDecompositionOfCompletePacking_length]
  rfl

theorem cycleDecompositionOfSteinerTripleSystem_cycleMean_le_six :
    (cycleDecompositionOfSteinerTripleSystem hn S).cycleMean ≤ 6 := by
  apply (cycleDecompositionOfSteinerTripleSystem hn S).cycleMean_le_of_forall_length_le 6
  intro t
  rw [cycleDecompositionOfSteinerTripleSystem_length]

theorem cycleDecompositionOfSteinerTripleSystem_cycleDispersion_le_six :
    CycleMixture.cycleDispersion (frame n hn).incidenceCount
      (cycleDecompositionOfSteinerTripleSystem hn S).length ≤ 6 := by
  apply (cycleDecompositionOfSteinerTripleSystem hn S).cycleDispersion_le_of_forall_length_le 6
  intro t
  rw [cycleDecompositionOfSteinerTripleSystem_length]

private theorem riskLower_antitone_exponent {a b : ℝ} (hab : a ≤ b) :
    1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) := by
  have hexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hsqrt : Real.sqrt (Real.exp a - 1) ≤ Real.sqrt (Real.exp b - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- The all-pairs testing lower bound obtained from a Steiner triple system.
Every cycle has the source length bound `6`, so this is the `α = 6` branch
of Section 7.2 before an existence theorem chooses a system for each
admissible number of items. -/
theorem productTestingLowerBound_ofSteinerTripleSystem
    (S : AppliedModelingLib.Foundations.Combinatorics.SteinerTripleSystem (Fin n))
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hsmall : 12 * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame n hn) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (6 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            ((frame n hn).incidenceCount : ℝ)) - 1)) := by
  let D := cycleDecompositionOfSteinerTripleSystem hn S
  let W : D.AlternatingCycleWitness := by
    simpa [D] using
      cycleDecompositionOfSteinerTripleSystem_alternatingCycleWitness hn S
  let d : ℝ := ((frame n hn).incidenceCount : ℝ)
  have hmean : D.cycleMean ≤ 6 := by
    simpa [D] using cycleDecompositionOfSteinerTripleSystem_cycleMean_le_six hn S
  have hdispersion :
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length ≤ 6 := by
    simpa [D] using cycleDecompositionOfSteinerTripleSystem_cycleDispersion_le_six hn S
  have hsmallD : 2 * D.cycleMean * δ ≤ 1 := by
    calc
      2 * D.cycleMean * δ = D.cycleMean * (2 * δ) := by ring
      _ ≤ 6 * (2 * δ) :=
        mul_le_mul_of_nonneg_right hmean (by positivity)
      _ = 12 * δ := by ring
      _ ≤ 1 := hsmall
  have hbase := D.theorem1_productTestingLowerBound W δ hδ_nonneg hsmallD N
  let a : ℝ :=
    (8 * D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length *
        (N : ℝ) ^ 2 * δ ^ 4) / d
  let b : ℝ := (8 * (6 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d
  have hdispersion_nonneg : 0 ≤
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length := by
    unfold CycleMixture.cycleDispersion
    positivity
  have hmean_pow : D.cycleMean ^ 4 ≤ (6 : ℝ) ^ 4 :=
    pow_le_pow_left₀ D.cycleMean_pos.le hmean 4
  have hproduct : D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length ≤ (6 : ℝ) ^ 5 := by
    calc
      D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length ≤
          (6 : ℝ) ^ 4 *
            CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length :=
        mul_le_mul_of_nonneg_right hmean_pow hdispersion_nonneg
      _ ≤ (6 : ℝ) ^ 4 * 6 :=
        mul_le_mul_of_nonneg_left hdispersion (pow_nonneg (by norm_num) 4)
      _ = (6 : ℝ) ^ 5 := by ring
  have hfactor : 0 ≤ 8 * (N : ℝ) ^ 2 * δ ^ 4 := by positivity
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast (frame n hn).incidenceCount_pos
  have hab : a ≤ b := by
    dsimp [a, b]
    calc
      (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length *
            (N : ℝ) ^ 2 * δ ^ 4) / d =
          (D.cycleMean ^ 4 *
            CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length) *
              (8 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
      _ ≤ (6 : ℝ) ^ 5 * (8 * (N : ℝ) ^ 2 * δ ^ 4) / d :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hproduct hfactor) hdpos.le
      _ = (8 * (6 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
  have hlower :
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
        1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) :=
    riskLower_antitone_exponent hab
  intro φ
  obtain ⟨q, hseparated, herror⟩ := hbase φ
  refine ⟨q, hseparated, ?_⟩
  apply hlower.trans
  simpa [a, d] using herror

/-- The same conditional all-pairs lower bound with the source identity
`d = n(n-1)` substituted into its denominator. -/
theorem productTestingLowerBound_ofSteinerTripleSystem_mul_pred
    (S : AppliedModelingLib.Foundations.Combinatorics.SteinerTripleSystem (Fin n))
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hsmall : 12 * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame n hn) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (6 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            ((n * (n - 1) : ℕ) : ℝ)) - 1)) := by
  simpa only [incidenceCount_eq_mul_pred] using
    productTestingLowerBound_ofSteinerTripleSystem hn S δ hδ_nonneg hsmall N

/-- The source's all-pairs lower bound for the Kirkman cardinalities.  The
Steiner system is the explicit Feder--Subi/Kirkman construction in the shared
combinatorics library, rather than a remaining existence assumption. -/
noncomputable def kirkmanSteinerTripleSystem (n : ℕ)
  (hgood : n % 6 = 1 ∨ n % 6 = 3) :
    AppliedModelingLib.Foundations.Combinatorics.SteinerTripleSystem (Fin n) :=
  (AppliedModelingLib.Foundations.Combinatorics.SteinerTripleSystem.steinerTripleSystem_exists_of_modSix
    n hgood).some

/-- The all-pairs product-testing lower bound on every `n ≡ 1,3 (mod 6)`
cardinality, with its exact incidence count substituted. -/
theorem productTestingLowerBound_of_modSix
    (hgood : n % 6 = 1 ∨ n % 6 = 3)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hsmall : 12 * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame n hn) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (6 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            ((n * (n - 1) : ℕ) : ℝ)) - 1)) :=
  productTestingLowerBound_ofSteinerTripleSystem_mul_pred hn
    (kirkmanSteinerTripleSystem n hgood) δ hδ_nonneg hsmall N

private theorem cycleObservation_item_mem_support (t : S.Triangle) (e : Fin 6) :
    (cycleObservation hn S t e).2.1 ∈ S.support t := by
  fin_cases e
  · simpa [cycleObservation] using S.vertex_mem_support t 0
  · simpa [cycleObservation] using S.vertex_mem_support t 1
  · simpa [cycleObservation] using S.vertex_mem_support t 1
  · simpa [cycleObservation] using S.vertex_mem_support t 2
  · simpa [cycleObservation] using S.vertex_mem_support t 2
  · simpa [cycleObservation] using S.vertex_mem_support t 0

private theorem cycleObservation_set_member_mem_support (t : S.Triangle) (e : Fin 6)
    (x : Fin n) (hx : x ∈ (F hn).members (cycleObservation hn S t e).1) :
    x ∈ S.support t := by
  fin_cases e
  · change x ∈ ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) at hx
    have hx' : x = triangleVertex S t 0 ∨ x = triangleVertex S t 1 := by simpa using hx
    rcases hx' with hx | hx
    · simpa [hx] using S.vertex_mem_support t 0
    · simpa [hx] using S.vertex_mem_support t 1
  · change x ∈ ({triangleVertex S t 0, triangleVertex S t 1} : Finset (Fin n)) at hx
    have hx' : x = triangleVertex S t 0 ∨ x = triangleVertex S t 1 := by simpa using hx
    rcases hx' with hx | hx
    · simpa [hx] using S.vertex_mem_support t 0
    · simpa [hx] using S.vertex_mem_support t 1
  · change x ∈ ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) at hx
    have hx' : x = triangleVertex S t 1 ∨ x = triangleVertex S t 2 := by simpa using hx
    rcases hx' with hx | hx
    · simpa [hx] using S.vertex_mem_support t 1
    · simpa [hx] using S.vertex_mem_support t 2
  · change x ∈ ({triangleVertex S t 1, triangleVertex S t 2} : Finset (Fin n)) at hx
    have hx' : x = triangleVertex S t 1 ∨ x = triangleVertex S t 2 := by simpa using hx
    rcases hx' with hx | hx
    · simpa [hx] using S.vertex_mem_support t 1
    · simpa [hx] using S.vertex_mem_support t 2
  · change x ∈ ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) at hx
    have hx' : x = triangleVertex S t 2 ∨ x = triangleVertex S t 0 := by simpa using hx
    rcases hx' with hx | hx
    · simpa [hx] using S.vertex_mem_support t 2
    · simpa [hx] using S.vertex_mem_support t 0
  · change x ∈ ({triangleVertex S t 2, triangleVertex S t 0} : Finset (Fin n)) at hx
    have hx' : x = triangleVertex S t 2 ∨ x = triangleVertex S t 0 := by simpa using hx
    rcases hx' with hx | hx
    · simpa [hx] using S.vertex_mem_support t 2
    · simpa [hx] using S.vertex_mem_support t 0

end TriangleBridge

end AllPairs

end SeshadriUgander2020IIATesting
