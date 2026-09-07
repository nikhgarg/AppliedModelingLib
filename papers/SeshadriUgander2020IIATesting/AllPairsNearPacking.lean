import SeshadriUgander2020IIATesting.AllPairs
import AppliedModelingLib.Foundations.Combinatorics.TrianglePackingConstructions

/-!
# All-pairs cycles from a four-cycle-leave triangle packing

Feder--Subi's near-decomposition leaves four item pairs arranged as one
four-cycle.  In the all-pairs comparison incidence graph those four choice
nodes and their item incidences form one alternating eight-cycle; every packed
triangle supplies the usual alternating six-cycle.
-/

namespace SeshadriUgander2020IIATesting

namespace AllPairs

open scoped Sym2
open AppliedModelingLib.Foundations.Graph
open AppliedModelingLib.Foundations.Combinatorics

namespace NearPackingBridge

variable {n : ℕ} (hn : 2 ≤ n)
variable (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
variable (hleave : P.LeavesFourCycle v)

private noncomputable abbrev F := frame n hn

private theorem fourCycleNext_ne (i : Fin 4) :
    TrianglePacking.fourCycleNext i ≠ i := by
  fin_cases i <;> decide

private theorem residualVertex_ne_next
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) (i : Fin 4) :
    v i ≠ v (TrianglePacking.fourCycleNext i) := by
  intro h
  exact fourCycleNext_ne i (hleave.1 h).symm

private theorem residualVertex_ne
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) {i j : Fin 4} (hij : i ≠ j) :
    v i ≠ v j := by
  intro h
  exact hij (hleave.1 h)

/-- The all-pairs choice vertex associated to one uncovered four-cycle edge. -/
private noncomputable def residualChoice
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) (i : Fin 4) : ChoiceSet n :=
  pair n (residualVertex_ne_next P v hleave i)

private theorem residualChoice_injective
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) :
  Function.Injective (residualChoice P v hleave) := by
  intro i j hij
  have hfinset := congrArg Subtype.val hij
  change ({v i, v (TrianglePacking.fourCycleNext i)} : Finset (Fin n)) =
    {v j, v (TrianglePacking.fourCycleNext j)} at hfinset
  have hset : ({v i, v (TrianglePacking.fourCycleNext i)} : Set (Fin n)) =
      {v j, v (TrianglePacking.fourCycleNext j)} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun q : Finset (Fin n) => (q : Set (Fin n))) hfinset
  rcases Set.pair_eq_pair_iff.mp hset with hforward | hreverse
  · exact hleave.1 hforward.1
  · exfalso
    have hdouble : i = TrianglePacking.fourCycleNext
        (TrianglePacking.fourCycleNext i) := by
      calc
        i = TrianglePacking.fourCycleNext j := hleave.1 hreverse.1
        _ = TrianglePacking.fourCycleNext (TrianglePacking.fourCycleNext i) := by
          rw [hleave.1 hreverse.2]
    fin_cases i <;> norm_num [TrianglePacking.fourCycleNext] at hdouble

private theorem residualChoice_ne
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) {i j : Fin 4} (hij : i ≠ j) :
    residualChoice P v hleave i ≠ residualChoice P v hleave j := by
  intro h
  exact hij (residualChoice_injective P v hleave h)

private noncomputable def residualCycleTail
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) :
    (F hn).incidenceGraph.Walk (Sum.inl (v 1))
      (Sum.inr (residualChoice P v hleave 0)) :=
  SimpleGraph.Walk.cons' (Sum.inl (v 1)) (Sum.inr (residualChoice P v hleave 1))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 1 ∈ (F hn).members (residualChoice P v hleave 1)
      change v 1 ∈ ({v 1, v (TrianglePacking.fourCycleNext 1)} : Finset (Fin n))
      simp)
  (SimpleGraph.Walk.cons' (Sum.inr (residualChoice P v hleave 1)) (Sum.inl (v 2))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 2 ∈ (F hn).members (residualChoice P v hleave 1)
      change v 2 ∈ ({v 1, v (TrianglePacking.fourCycleNext 1)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext])
  (SimpleGraph.Walk.cons' (Sum.inl (v 2)) (Sum.inr (residualChoice P v hleave 2))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 2 ∈ (F hn).members (residualChoice P v hleave 2)
      change v 2 ∈ ({v 2, v (TrianglePacking.fourCycleNext 2)} : Finset (Fin n))
      simp)
  (SimpleGraph.Walk.cons' (Sum.inr (residualChoice P v hleave 2)) (Sum.inl (v 3))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 3 ∈ (F hn).members (residualChoice P v hleave 2)
      change v 3 ∈ ({v 2, v (TrianglePacking.fourCycleNext 2)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext])
  (SimpleGraph.Walk.cons' (Sum.inl (v 3)) (Sum.inr (residualChoice P v hleave 3))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 3 ∈ (F hn).members (residualChoice P v hleave 3)
      change v 3 ∈ ({v 3, v (TrianglePacking.fourCycleNext 3)} : Finset (Fin n))
      simp)
  (SimpleGraph.Walk.cons' (Sum.inr (residualChoice P v hleave 3)) (Sum.inl (v 0))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 0 ∈ (F hn).members (residualChoice P v hleave 3)
      change v 0 ∈ ({v 3, v (TrianglePacking.fourCycleNext 3)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext])
  (SimpleGraph.Walk.cons' (Sum.inl (v 0)) (Sum.inr (residualChoice P v hleave 0))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 0 ∈ (F hn).members (residualChoice P v hleave 0)
      change v 0 ∈ ({v 0, v (TrianglePacking.fourCycleNext 0)} : Finset (Fin n))
      simp)
  SimpleGraph.Walk.nil))))))

private noncomputable def residualCycleWalk
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) :
    (F hn).incidenceGraph.Walk (Sum.inr (residualChoice P v hleave 0))
      (Sum.inr (residualChoice P v hleave 0)) :=
  SimpleGraph.Walk.cons' (Sum.inr (residualChoice P v hleave 0)) (Sum.inl (v 1))
    (Sum.inr (residualChoice P v hleave 0)) (by
      change v 1 ∈ (F hn).members (residualChoice P v hleave 0)
      change v 1 ∈ ({v 0, v (TrianglePacking.fourCycleNext 0)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext])
  (residualCycleTail hn P v hleave)

private theorem residualCycleTail_isPath
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) :
    (residualCycleTail hn P v hleave).IsPath := by
  have hv12 := residualVertex_ne P v hleave (show (1 : Fin 4) ≠ 2 by decide)
  have hv13 := residualVertex_ne P v hleave (show (1 : Fin 4) ≠ 3 by decide)
  have hv23 := residualVertex_ne P v hleave (show (2 : Fin 4) ≠ 3 by decide)
  have hv10 := residualVertex_ne P v hleave (show (1 : Fin 4) ≠ 0 by decide)
  have hv20 := residualVertex_ne P v hleave (show (2 : Fin 4) ≠ 0 by decide)
  have hv30 := residualVertex_ne P v hleave (show (3 : Fin 4) ≠ 0 by decide)
  have hc12 := residualChoice_ne P v hleave (show (1 : Fin 4) ≠ 2 by decide)
  have hc13 := residualChoice_ne P v hleave (show (1 : Fin 4) ≠ 3 by decide)
  have hc23 := residualChoice_ne P v hleave (show (2 : Fin 4) ≠ 3 by decide)
  have hc10 := residualChoice_ne P v hleave (show (1 : Fin 4) ≠ 0 by decide)
  have hc20 := residualChoice_ne P v hleave (show (2 : Fin 4) ≠ 0 by decide)
  have hc30 := residualChoice_ne P v hleave (show (3 : Fin 4) ≠ 0 by decide)
  rw [SimpleGraph.Walk.isPath_def]
  change [Sum.inl (v 1), Sum.inr (residualChoice P v hleave 1),
    Sum.inl (v 2), Sum.inr (residualChoice P v hleave 2),
    Sum.inl (v 3), Sum.inr (residualChoice P v hleave 3),
    Sum.inl (v 0), Sum.inr (residualChoice P v hleave 0)].Nodup
  simp [hv12, hv13, hv23, hv10, hv20, hv30,
    hc12, hc13, hc23, hc10, hc20, hc30]

private theorem residualCycleWalk_isCycle
    (P : TrianglePacking (Fin n)) (v : Fin 4 → Fin n)
    (hleave : P.LeavesFourCycle v) :
    (residualCycleWalk hn P v hleave).IsCycle := by
  unfold residualCycleWalk
  change (SimpleGraph.Walk.cons _ (residualCycleTail hn P v hleave)).IsCycle
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨residualCycleTail_isPath hn P v hleave, ?_⟩
  have hv10 := residualVertex_ne P v hleave (show (1 : Fin 4) ≠ 0 by decide)
  have hc01 := residualChoice_ne P v hleave (show (0 : Fin 4) ≠ 1 by decide)
  have hc02 := residualChoice_ne P v hleave (show (0 : Fin 4) ≠ 2 by decide)
  have hc03 := residualChoice_ne P v hleave (show (0 : Fin 4) ≠ 3 by decide)
  change s(Sum.inr (residualChoice P v hleave 0), Sum.inl (v 1)) ∉
    [s(Sum.inl (v 1), Sum.inr (residualChoice P v hleave 1)),
      s(Sum.inr (residualChoice P v hleave 1), Sum.inl (v 2)),
      s(Sum.inl (v 2), Sum.inr (residualChoice P v hleave 2)),
      s(Sum.inr (residualChoice P v hleave 2), Sum.inl (v 3)),
      s(Sum.inl (v 3), Sum.inr (residualChoice P v hleave 3)),
      s(Sum.inr (residualChoice P v hleave 3), Sum.inl (v 0)),
      s(Sum.inl (v 0), Sum.inr (residualChoice P v hleave 0))]
  simp [hv10, hc01, hc02, hc03]

section TriangleCycles

private def nearCycleEdge : Fin 6 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2

private def nearCycleEndpoint (e : Fin 6) : Fin 3 :=
  if e = 0 then 0
  else if e = 1 then 1
  else if e = 2 then 1
  else if e = 3 then 2
  else if e = 4 then 2
  else 0

private theorem nearCycleEdge_endpoint_injective :
    Function.Injective (fun e : Fin 6 =>
      (nearCycleEdge e, nearCycleEndpoint e)) := by
  intro e f h
  fin_cases e <;> fin_cases f <;> simp [nearCycleEdge, nearCycleEndpoint] at h ⊢

private def nearTriangleVertex (t : P.Triangle) (i : Fin 3) : Fin n := P.vertex t i

private theorem nearTriangleVertex_ne {t : P.Triangle} {i j : Fin 3} (hij : i ≠ j) :
    nearTriangleVertex P t i ≠ nearTriangleVertex P t j := by
  intro h
  exact hij (P.vertex_injective t h)

private noncomputable def nearEdgeChoice (t : P.Triangle) (i : Fin 3) : ChoiceSet n :=
  if i = 0 then
    pair n (nearTriangleVertex_ne P (t := t) (show (0 : Fin 3) ≠ 1 by decide))
  else if i = 1 then
    pair n (nearTriangleVertex_ne P (t := t) (show (1 : Fin 3) ≠ 2 by decide))
  else
    pair n (nearTriangleVertex_ne P (t := t) (show (2 : Fin 3) ≠ 0 by decide))

private noncomputable def nearCycleObservation (t : P.Triangle) (e : Fin 6) :
    (F hn).Observation :=
  if e = 0 then
    ⟨nearEdgeChoice P t 0,
      ⟨nearTriangleVertex P t 0,
        by change nearTriangleVertex P t 0 ∈
          ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)); simp⟩⟩
  else if e = 1 then
    ⟨nearEdgeChoice P t 0,
      ⟨nearTriangleVertex P t 1,
        by change nearTriangleVertex P t 1 ∈
          ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)); simp⟩⟩
  else if e = 2 then
    ⟨nearEdgeChoice P t 1,
      ⟨nearTriangleVertex P t 1,
        by change nearTriangleVertex P t 1 ∈
          ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)); simp⟩⟩
  else if e = 3 then
    ⟨nearEdgeChoice P t 1,
      ⟨nearTriangleVertex P t 2,
        by change nearTriangleVertex P t 2 ∈
          ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)); simp⟩⟩
  else if e = 4 then
    ⟨nearEdgeChoice P t 2,
      ⟨nearTriangleVertex P t 2,
        by change nearTriangleVertex P t 2 ∈
          ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)); simp⟩⟩
  else
    ⟨nearEdgeChoice P t 2,
      ⟨nearTriangleVertex P t 0,
        by change nearTriangleVertex P t 0 ∈
          ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)); simp⟩⟩

private noncomputable def nearTriangleCycleTail (t : P.Triangle) :
    (F hn).incidenceGraph.Walk (Sum.inl (nearTriangleVertex P t 1))
      (Sum.inr (nearEdgeChoice P t 0)) :=
  SimpleGraph.Walk.cons' (Sum.inl (nearTriangleVertex P t 1)) (Sum.inr (nearEdgeChoice P t 1))
    (Sum.inr (nearEdgeChoice P t 0)) (by
      change nearTriangleVertex P t 1 ∈ (F hn).members (nearEdgeChoice P t 1)
      change nearTriangleVertex P t 1 ∈
        ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n))
      simp)
  (SimpleGraph.Walk.cons' (Sum.inr (nearEdgeChoice P t 1)) (Sum.inl (nearTriangleVertex P t 2))
    (Sum.inr (nearEdgeChoice P t 0)) (by
      change nearTriangleVertex P t 2 ∈ (F hn).members (nearEdgeChoice P t 1)
      change nearTriangleVertex P t 2 ∈
        ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n))
      simp)
  (SimpleGraph.Walk.cons' (Sum.inl (nearTriangleVertex P t 2)) (Sum.inr (nearEdgeChoice P t 2))
    (Sum.inr (nearEdgeChoice P t 0)) (by
      change nearTriangleVertex P t 2 ∈ (F hn).members (nearEdgeChoice P t 2)
      change nearTriangleVertex P t 2 ∈
        ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n))
      simp)
  (SimpleGraph.Walk.cons' (Sum.inr (nearEdgeChoice P t 2)) (Sum.inl (nearTriangleVertex P t 0))
    (Sum.inr (nearEdgeChoice P t 0)) (by
      change nearTriangleVertex P t 0 ∈ (F hn).members (nearEdgeChoice P t 2)
      change nearTriangleVertex P t 0 ∈
        ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n))
      simp)
  (SimpleGraph.Walk.cons' (Sum.inl (nearTriangleVertex P t 0)) (Sum.inr (nearEdgeChoice P t 0))
    (Sum.inr (nearEdgeChoice P t 0)) (by
      change nearTriangleVertex P t 0 ∈ (F hn).members (nearEdgeChoice P t 0)
      change nearTriangleVertex P t 0 ∈
        ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n))
      simp)
  SimpleGraph.Walk.nil))))

private noncomputable def nearTriangleCycleWalk (t : P.Triangle) :
    (F hn).incidenceGraph.Walk (Sum.inr (nearEdgeChoice P t 0))
      (Sum.inr (nearEdgeChoice P t 0)) :=
  SimpleGraph.Walk.cons' (Sum.inr (nearEdgeChoice P t 0)) (Sum.inl (nearTriangleVertex P t 1))
    (Sum.inr (nearEdgeChoice P t 0)) (by
      change nearTriangleVertex P t 1 ∈ (F hn).members (nearEdgeChoice P t 0)
      change nearTriangleVertex P t 1 ∈
        ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n))
      simp)
  (nearTriangleCycleTail hn P t)

private theorem nearCycleObservation_choice_eq_edgeChoice (t : P.Triangle) (e : Fin 6) :
    (nearCycleObservation hn P t e).1 = nearEdgeChoice P t (nearCycleEdge e) := by
  fin_cases e <;> rfl

private theorem nearCycleObservation_item_eq_triangleVertex (t : P.Triangle) (e : Fin 6) :
    (nearCycleObservation hn P t e).2.1 =
      nearTriangleVertex P t (nearCycleEndpoint e) := by
  fin_cases e <;> rfl

private theorem nearEdgeChoice_injective (t : P.Triangle) :
    Function.Injective (nearEdgeChoice P t) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals exfalso
  all_goals have hset := congrArg Subtype.val hij
  · change ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)) =
        {nearTriangleVertex P t 1, nearTriangleVertex P t 2} at hset
    have hmem : nearTriangleVertex P t 0 ∈
        ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
  · change ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)) =
        {nearTriangleVertex P t 2, nearTriangleVertex P t 0} at hset
    have hmem : nearTriangleVertex P t 1 ∈
        ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h.symm
  · change ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)) =
        {nearTriangleVertex P t 0, nearTriangleVertex P t 1} at hset
    have hmem : nearTriangleVertex P t 2 ∈
        ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
  · change ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)) =
        {nearTriangleVertex P t 2, nearTriangleVertex P t 0} at hset
    have hmem : nearTriangleVertex P t 1 ∈
        ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h.symm
  · change ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)) =
        {nearTriangleVertex P t 0, nearTriangleVertex P t 1} at hset
    have hmem : nearTriangleVertex P t 2 ∈
        ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
  · change ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)) =
        {nearTriangleVertex P t 1, nearTriangleVertex P t 2} at hset
    have hmem : nearTriangleVertex P t 0 ∈
        ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)) := by
      rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h
    · exact nearTriangleVertex_ne P (t := t) (by decide) h

private theorem nearTriangleCycleTail_isPath (t : P.Triangle) :
    (nearTriangleCycleTail hn P t).IsPath := by
  have h01 : nearEdgeChoice P t 0 ≠ nearEdgeChoice P t 1 := by
    intro h; exact (by decide : (0 : Fin 3) ≠ 1) (nearEdgeChoice_injective P t h)
  have h02 : nearEdgeChoice P t 0 ≠ nearEdgeChoice P t 2 := by
    intro h; exact (by decide : (0 : Fin 3) ≠ 2) (nearEdgeChoice_injective P t h)
  have h12 : nearEdgeChoice P t 1 ≠ nearEdgeChoice P t 2 := by
    intro h; exact (by decide : (1 : Fin 3) ≠ 2) (nearEdgeChoice_injective P t h)
  rw [SimpleGraph.Walk.isPath_def]
  change [Sum.inl (nearTriangleVertex P t 1), Sum.inr (nearEdgeChoice P t 1),
    Sum.inl (nearTriangleVertex P t 2), Sum.inr (nearEdgeChoice P t 2),
    Sum.inl (nearTriangleVertex P t 0), Sum.inr (nearEdgeChoice P t 0)].Nodup
  have h10 : nearEdgeChoice P t 1 ≠ nearEdgeChoice P t 0 := h01.symm
  have h20 : nearEdgeChoice P t 2 ≠ nearEdgeChoice P t 0 := h02.symm
  have hv01 := nearTriangleVertex_ne P (t := t) (show (0 : Fin 3) ≠ 1 by decide)
  have hv02 := nearTriangleVertex_ne P (t := t) (show (0 : Fin 3) ≠ 2 by decide)
  have hv12 := nearTriangleVertex_ne P (t := t) (show (1 : Fin 3) ≠ 2 by decide)
  have hv10 := hv01.symm
  have hv20 := hv02.symm
  simp [h12, h10, h20, hv12, hv10, hv20]

private theorem nearTriangleCycleWalk_isCycle (t : P.Triangle) :
    (nearTriangleCycleWalk hn P t).IsCycle := by
  unfold nearTriangleCycleWalk
  change (SimpleGraph.Walk.cons _ (nearTriangleCycleTail hn P t)).IsCycle
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨nearTriangleCycleTail_isPath hn P t, ?_⟩
  have h01 : nearEdgeChoice P t 0 ≠ nearEdgeChoice P t 1 := by
    intro h; exact (by decide : (0 : Fin 3) ≠ 1) (nearEdgeChoice_injective P t h)
  have h02 : nearEdgeChoice P t 0 ≠ nearEdgeChoice P t 2 := by
    intro h; exact (by decide : (0 : Fin 3) ≠ 2) (nearEdgeChoice_injective P t h)
  have hv01 := nearTriangleVertex_ne P (t := t) (show (0 : Fin 3) ≠ 1 by decide)
  have hv12 := nearTriangleVertex_ne P (t := t) (show (1 : Fin 3) ≠ 2 by decide)
  have hv10 := hv01.symm
  change s(Sum.inr (nearEdgeChoice P t 0), Sum.inl (nearTriangleVertex P t 1)) ∉
    [s(Sum.inl (nearTriangleVertex P t 1), Sum.inr (nearEdgeChoice P t 1)),
      s(Sum.inr (nearEdgeChoice P t 1), Sum.inl (nearTriangleVertex P t 2)),
      s(Sum.inl (nearTriangleVertex P t 2), Sum.inr (nearEdgeChoice P t 2)),
      s(Sum.inr (nearEdgeChoice P t 2), Sum.inl (nearTriangleVertex P t 0)),
      s(Sum.inl (nearTriangleVertex P t 0), Sum.inr (nearEdgeChoice P t 0))]
  simp [h01, h02, hv12, hv10]

private theorem nearMemEdgeChoice_vertex (t : P.Triangle) (i : Fin 3)
    (x : Fin n) (hx : x ∈ (nearEdgeChoice P t i : Finset (Fin n))) :
    ∃ j : Fin 3, nearTriangleVertex P t j = x := by
  fin_cases i
  · change x ∈ ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩
  · change x ∈ ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ⟨1, hx.symm⟩
    · exact ⟨2, hx.symm⟩
  · change x ∈ ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ⟨2, hx.symm⟩
    · exact ⟨0, hx.symm⟩

/-- Distinct packed triangles cannot share an all-pairs choice vertex. -/
private theorem nearEdgeChoice_eq_implies_triangle_eq {t u : P.Triangle}
    {i j : Fin 3} (h : nearEdgeChoice P t i = nearEdgeChoice P u j) : t = u := by
  fin_cases i
  · let x := nearTriangleVertex P t 0
    let y := nearTriangleVertex P t 1
    have hxy : x ≠ y := nearTriangleVertex_ne P (t := t) (by decide)
    have hx : x ∈ (nearEdgeChoice P t 0 : Finset (Fin n)) := by
      change nearTriangleVertex P t 0 ∈
        ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)); simp
    have hy : y ∈ (nearEdgeChoice P t 0 : Finset (Fin n)) := by
      change nearTriangleVertex P t 1 ∈
        ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)); simp
    exact P.coversPair_unique hxy ⟨0, rfl⟩ ⟨1, rfl⟩
      (nearMemEdgeChoice_vertex P u j x (by rw [← h]; exact hx))
      (nearMemEdgeChoice_vertex P u j y (by rw [← h]; exact hy))
  · let x := nearTriangleVertex P t 1
    let y := nearTriangleVertex P t 2
    have hxy : x ≠ y := nearTriangleVertex_ne P (t := t) (by decide)
    have hx : x ∈ (nearEdgeChoice P t 1 : Finset (Fin n)) := by
      change nearTriangleVertex P t 1 ∈
        ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)); simp
    have hy : y ∈ (nearEdgeChoice P t 1 : Finset (Fin n)) := by
      change nearTriangleVertex P t 2 ∈
        ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)); simp
    exact P.coversPair_unique hxy ⟨1, rfl⟩ ⟨2, rfl⟩
      (nearMemEdgeChoice_vertex P u j x (by rw [← h]; exact hx))
      (nearMemEdgeChoice_vertex P u j y (by rw [← h]; exact hy))
  · let x := nearTriangleVertex P t 2
    let y := nearTriangleVertex P t 0
    have hxy : x ≠ y := nearTriangleVertex_ne P (t := t) (by decide)
    have hx : x ∈ (nearEdgeChoice P t 2 : Finset (Fin n)) := by
      change nearTriangleVertex P t 2 ∈
        ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)); simp
    have hy : y ∈ (nearEdgeChoice P t 2 : Finset (Fin n)) := by
      change nearTriangleVertex P t 0 ∈
        ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)); simp
    exact P.coversPair_unique hxy ⟨2, rfl⟩ ⟨0, rfl⟩
      (nearMemEdgeChoice_vertex P u j x (by rw [← h]; exact hx))
      (nearMemEdgeChoice_vertex P u j y (by rw [← h]; exact hy))

private theorem nearCycleObservation_injective (t : P.Triangle) :
    Function.Injective (nearCycleObservation hn P t) := by
  intro e f hef
  have hchoice : (nearCycleObservation hn P t e).1 = (nearCycleObservation hn P t f).1 :=
    congrArg Sigma.fst hef
  rw [nearCycleObservation_choice_eq_edgeChoice, nearCycleObservation_choice_eq_edgeChoice] at hchoice
  have hedge : nearCycleEdge e = nearCycleEdge f := nearEdgeChoice_injective P t hchoice
  have hitem : (nearCycleObservation hn P t e).2.1 = (nearCycleObservation hn P t f).2.1 :=
    congrArg (fun o => o.2.1) hef
  have hendpoint : nearCycleEndpoint e = nearCycleEndpoint f := by
    apply P.vertex_injective t
    change nearTriangleVertex P t (nearCycleEndpoint e) = nearTriangleVertex P t (nearCycleEndpoint f)
    rw [← nearCycleObservation_item_eq_triangleVertex hn P t e,
      ← nearCycleObservation_item_eq_triangleVertex hn P t f]
    exact hitem
  exact nearCycleEdge_endpoint_injective (Prod.ext hedge hendpoint)

private theorem globalNearCycleObservation_injective :
    Function.Injective (fun q : Sigma fun _ : P.Triangle => Fin 6 =>
      nearCycleObservation hn P q.1 q.2) := by
  rintro ⟨t, e⟩ ⟨u, f⟩ h
  have hchoice : nearEdgeChoice P t (nearCycleEdge e) = nearEdgeChoice P u (nearCycleEdge f) := by
    rw [← nearCycleObservation_choice_eq_edgeChoice hn P t e,
      ← nearCycleObservation_choice_eq_edgeChoice hn P u f]
    exact congrArg Sigma.fst h
  have htu : t = u := nearEdgeChoice_eq_implies_triangle_eq P hchoice
  subst u
  have hef : e = f := nearCycleObservation_injective hn P t h
  subst f
  rfl

private def nearCycleObservationPosition (e : Fin 6) : Fin 6 :=
  ⟨(e.1 + 5) % 6, Nat.mod_lt _ (by decide)⟩

private def nearEdgePositionObservation (e : Fin 6) : Fin 6 :=
  ⟨(e.1 + 1) % 6, Nat.mod_lt _ (by decide)⟩

private theorem nearCycleObservationPosition_edgePositionObservation (e : Fin 6) :
    nearCycleObservationPosition (nearEdgePositionObservation e) = e := by
  fin_cases e <;> rfl

private theorem observationEdge_nearCycleObservation_eq_edgeAt
    (t : P.Triangle) (e : Fin 6) :
    (F hn).observationEdge (nearCycleObservation hn P t e) =
      AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (nearTriangleCycleWalk hn P t)
        (nearCycleObservationPosition e) := by
  fin_cases e
  · rfl
  · apply Sym2.eq_iff.mpr; exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · apply Sym2.eq_iff.mpr; exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · apply Sym2.eq_iff.mpr; exact Or.inr ⟨rfl, rfl⟩

private noncomputable def nearTriangleCyclePacking :
    PartialSimpleCyclePacking (F hn).incidenceGraph 6 where
  Cycle := P.Triangle
  instFintypeCycle := inferInstance
  instDecidableEqCycle := inferInstance
  walk := fun t => ⟨Sum.inr (nearEdgeChoice P t 0), nearTriangleCycleWalk hn P t⟩
  isCycle := fun t => nearTriangleCycleWalk_isCycle hn P t
  length_le := by
    intro t
    change (nearTriangleCycleWalk hn P t).length ≤ 6
    rfl
  pairwiseDisjoint := by
    intro t _ u _ htu
    apply Finset.disjoint_left.2
    intro edge hedget hedgeu
    change edge ∈ (nearTriangleCycleWalk hn P t).edges.toFinset at hedget
    change edge ∈ (nearTriangleCycleWalk hn P u).edges.toFinset at hedgeu
    let positionT : Fin 6 :=
      (AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (nearTriangleCycleWalk_isCycle hn P t)).symm ⟨edge, hedget⟩
    let positionU : Fin 6 :=
      (AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (nearTriangleCycleWalk_isCycle hn P u)).symm ⟨edge, hedgeu⟩
    have hpositionT :
        AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (nearTriangleCycleWalk hn P t)
          positionT = edge := by
      change ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (nearTriangleCycleWalk_isCycle hn P t) positionT).1) = edge
      exact congrArg Subtype.val
        ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
          (nearTriangleCycleWalk_isCycle hn P t)).apply_symm_apply ⟨edge, hedget⟩)
    have hpositionU :
        AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (nearTriangleCycleWalk hn P u)
          positionU = edge := by
      change ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (nearTriangleCycleWalk_isCycle hn P u) positionU).1) = edge
      exact congrArg Subtype.val
        ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
          (nearTriangleCycleWalk_isCycle hn P u)).apply_symm_apply ⟨edge, hedgeu⟩)
    have hobsT :
        (F hn).observationEdge
          (nearCycleObservation hn P t (nearEdgePositionObservation positionT)) = edge := by
      rw [observationEdge_nearCycleObservation_eq_edgeAt,
        nearCycleObservationPosition_edgePositionObservation]
      exact hpositionT
    have hobsU :
        (F hn).observationEdge
          (nearCycleObservation hn P u (nearEdgePositionObservation positionU)) = edge := by
      rw [observationEdge_nearCycleObservation_eq_edgeAt,
        nearCycleObservationPosition_edgePositionObservation]
      exact hpositionU
    have hobs : nearCycleObservation hn P t (nearEdgePositionObservation positionT) =
        nearCycleObservation hn P u (nearEdgePositionObservation positionU) :=
      (F hn).observationEdge_injective (hobsT.trans hobsU.symm)
    have htu' : (⟨t, nearEdgePositionObservation positionT⟩ :
        Sigma fun _ : P.Triangle => Fin 6) =
        ⟨u, nearEdgePositionObservation positionU⟩ :=
      globalNearCycleObservation_injective hn P hobs
    exact htu (congrArg Sigma.fst htu')

private theorem nearCycleObservation_eq_of_choice_and_item
    (t : P.Triangle) (e : Fin 6) (x y : Fin n) (hxy : x ≠ y)
    (hchoice : (F hn).members (nearCycleObservation hn P t e).1 = {x, y})
    (hitem : (nearCycleObservation hn P t e).2.1 = x) :
    nearCycleObservation hn P t e =
      ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ := by
  apply Sigma.ext
  · apply Subtype.ext
    exact hchoice
  · apply (Subtype.heq_iff_coe_eq (fun candidate => by
      change candidate ∈ (F hn).members (nearCycleObservation hn P t e).1 ↔
        candidate ∈ (pair n hxy : Finset (Fin n))
      rw [hchoice]
      rfl)).mpr
    exact hitem

private theorem exists_nearCycleObservation_eq_pair (x y : Fin n) (hxy : x ≠ y)
    (hcover : P.CoversPair x y) :
    ∃ (t : P.Triangle) (e : Fin 6),
      nearCycleObservation hn P t e =
        ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ := by
  obtain ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hcover
  change nearTriangleVertex P t i = x at hi
  change nearTriangleVertex P t j = y at hj
  have hij : i ≠ j := by
    intro h
    apply hxy
    calc
      x = nearTriangleVertex P t i := hi.symm
      _ = nearTriangleVertex P t j := congrArg (nearTriangleVertex P t) h
      _ = y := hj
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change nearTriangleVertex P t 0 = x at hi
    change nearTriangleVertex P t 1 = y at hj
    refine ⟨t, 0, nearCycleObservation_eq_of_choice_and_item hn P t 0 x y hxy ?_ hi⟩
    change ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)) = {x, y}
    rw [hi, hj]
  · change nearTriangleVertex P t 0 = x at hi
    change nearTriangleVertex P t 2 = y at hj
    refine ⟨t, 5, nearCycleObservation_eq_of_choice_and_item hn P t 5 x y hxy ?_ hi⟩
    change ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)) = {x, y}
    rw [hj, hi]
    exact Finset.pair_comm _ _
  · change nearTriangleVertex P t 1 = x at hi
    change nearTriangleVertex P t 0 = y at hj
    refine ⟨t, 1, nearCycleObservation_eq_of_choice_and_item hn P t 1 x y hxy ?_ hi⟩
    change ({nearTriangleVertex P t 0, nearTriangleVertex P t 1} : Finset (Fin n)) = {x, y}
    rw [hj, hi]
    exact Finset.pair_comm _ _
  · exact (hij rfl).elim
  · change nearTriangleVertex P t 1 = x at hi
    change nearTriangleVertex P t 2 = y at hj
    refine ⟨t, 2, nearCycleObservation_eq_of_choice_and_item hn P t 2 x y hxy ?_ hi⟩
    change ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)) = {x, y}
    rw [hi, hj]
  · change nearTriangleVertex P t 2 = x at hi
    change nearTriangleVertex P t 0 = y at hj
    refine ⟨t, 4, nearCycleObservation_eq_of_choice_and_item hn P t 4 x y hxy ?_ hi⟩
    change ({nearTriangleVertex P t 2, nearTriangleVertex P t 0} : Finset (Fin n)) = {x, y}
    rw [hi, hj]
  · change nearTriangleVertex P t 2 = x at hi
    change nearTriangleVertex P t 1 = y at hj
    refine ⟨t, 3, nearCycleObservation_eq_of_choice_and_item hn P t 3 x y hxy ?_ hi⟩
    change ({nearTriangleVertex P t 1, nearTriangleVertex P t 2} : Finset (Fin n)) = {x, y}
    rw [hj, hi]
    exact Finset.pair_comm _ _
  · exact (hij rfl).elim

private theorem nearTriangleCyclePacking_covers_observation
    (x y : Fin n) (hxy : x ≠ y) (hcover : P.CoversPair x y) :
    (F hn).observationEdge ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ ∈
      (nearTriangleCyclePacking hn P).usedEdges := by
  obtain ⟨t, e, he⟩ := exists_nearCycleObservation_eq_pair hn P x y hxy hcover
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Finset.mem_univ _, ?_⟩
  change (F hn).observationEdge ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ ∈
    (nearTriangleCycleWalk hn P t).edges.toFinset
  rw [← he, observationEdge_nearCycleObservation_eq_edgeAt]
  apply List.mem_toFinset.mpr
  exact List.get_mem _ _

private def residualObservationChoiceIndex : Fin 8 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 3

private def residualObservationItemIndex : Fin 8 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 0

private noncomputable def residualCycleObservation (e : Fin 8) : (F hn).Observation :=
  match e with
  | 0 => ⟨residualChoice P v hleave 0, ⟨v 0, by
      change v 0 ∈ ({v 0, v (TrianglePacking.fourCycleNext 0)} : Finset (Fin n))
      simp⟩⟩
  | 1 => ⟨residualChoice P v hleave 0, ⟨v 1, by
      change v 1 ∈ ({v 0, v (TrianglePacking.fourCycleNext 0)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext]⟩⟩
  | 2 => ⟨residualChoice P v hleave 1, ⟨v 1, by
      change v 1 ∈ ({v 1, v (TrianglePacking.fourCycleNext 1)} : Finset (Fin n))
      simp⟩⟩
  | 3 => ⟨residualChoice P v hleave 1, ⟨v 2, by
      change v 2 ∈ ({v 1, v (TrianglePacking.fourCycleNext 1)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext]⟩⟩
  | 4 => ⟨residualChoice P v hleave 2, ⟨v 2, by
      change v 2 ∈ ({v 2, v (TrianglePacking.fourCycleNext 2)} : Finset (Fin n))
      simp⟩⟩
  | 5 => ⟨residualChoice P v hleave 2, ⟨v 3, by
      change v 3 ∈ ({v 2, v (TrianglePacking.fourCycleNext 2)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext]⟩⟩
  | 6 => ⟨residualChoice P v hleave 3, ⟨v 3, by
      change v 3 ∈ ({v 3, v (TrianglePacking.fourCycleNext 3)} : Finset (Fin n))
      simp⟩⟩
  | 7 => ⟨residualChoice P v hleave 3, ⟨v 0, by
      change v 0 ∈ ({v 3, v (TrianglePacking.fourCycleNext 3)} : Finset (Fin n))
      simp [TrianglePacking.fourCycleNext]⟩⟩

private theorem residualCycleObservation_choice_eq (e : Fin 8) :
    (residualCycleObservation hn P v hleave e).1 =
      residualChoice P v hleave (residualObservationChoiceIndex e) := by
  fin_cases e <;> rfl

private theorem residualCycleObservation_item_eq (e : Fin 8) :
    (residualCycleObservation hn P v hleave e).2.1 =
      v (residualObservationItemIndex e) := by
  fin_cases e <;> rfl

private theorem residualObservation_indices_injective :
    Function.Injective (fun e : Fin 8 =>
      (residualObservationChoiceIndex e, residualObservationItemIndex e)) := by
  intro e f h
  fin_cases e <;> fin_cases f <;>
    simp [residualObservationChoiceIndex, residualObservationItemIndex] at h ⊢

private theorem residualCycleObservation_injective :
    Function.Injective (residualCycleObservation hn P v hleave) := by
  intro e f hef
  have hchoice : (residualCycleObservation hn P v hleave e).1 =
      (residualCycleObservation hn P v hleave f).1 := congrArg Sigma.fst hef
  rw [residualCycleObservation_choice_eq, residualCycleObservation_choice_eq] at hchoice
  have hchoiceIndex : residualObservationChoiceIndex e = residualObservationChoiceIndex f :=
    residualChoice_injective P v hleave hchoice
  have hitem : (residualCycleObservation hn P v hleave e).2.1 =
      (residualCycleObservation hn P v hleave f).2.1 := congrArg (fun o => o.2.1) hef
  rw [residualCycleObservation_item_eq, residualCycleObservation_item_eq] at hitem
  have hitemIndex : residualObservationItemIndex e = residualObservationItemIndex f :=
    hleave.1 hitem
  exact residualObservation_indices_injective (Prod.ext hchoiceIndex hitemIndex)

private def residualCycleObservationPosition (e : Fin 8) : Fin 8 :=
  ⟨(e.1 + 7) % 8, Nat.mod_lt _ (by decide)⟩

private theorem observationEdge_residualCycleObservation_eq_edgeAt (e : Fin 8) :
    (F hn).observationEdge (residualCycleObservation hn P v hleave e) =
      AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (residualCycleWalk hn P v hleave)
        (residualCycleObservationPosition e) := by
  fin_cases e
  · rfl
  · apply Sym2.eq_iff.mpr; exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · apply Sym2.eq_iff.mpr; exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · apply Sym2.eq_iff.mpr; exact Or.inr ⟨rfl, rfl⟩
  · rfl
  · apply Sym2.eq_iff.mpr; exact Or.inr ⟨rfl, rfl⟩

private theorem residualCycleObservation_eq_of_choice_and_item
    (e : Fin 8) (x y : Fin n) (hxy : x ≠ y)
    (hchoice : (F hn).members (residualCycleObservation hn P v hleave e).1 = {x, y})
    (hitem : (residualCycleObservation hn P v hleave e).2.1 = x) :
    residualCycleObservation hn P v hleave e =
      ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ := by
  apply Sigma.ext
  · apply Subtype.ext
    exact hchoice
  · apply (Subtype.heq_iff_coe_eq (fun candidate => by
      change candidate ∈ (F hn).members (residualCycleObservation hn P v hleave e).1 ↔
        candidate ∈ (pair n hxy : Finset (Fin n))
      rw [hchoice]
      rfl)).mpr
    exact hitem

private theorem exists_residualCycleObservation_eq_pair
    (x y : Fin n) (hxy : x ≠ y) (r : Fin 4)
    (hpair : s(x, y) = s(v r, v (TrianglePacking.fourCycleNext r))) :
    ∃ e : Fin 8, residualCycleObservation hn P v hleave e =
      ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ := by
  rcases Sym2.eq_iff.mp hpair with hforward | hreverse
  · rcases hforward with ⟨rfl, rfl⟩
    fin_cases r
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨6, rfl⟩
  · rcases hreverse with ⟨rfl, rfl⟩
    fin_cases r
    · refine ⟨1, residualCycleObservation_eq_of_choice_and_item hn P v hleave 1 _ _ hxy ?_ rfl⟩
      exact Finset.pair_comm _ _
    · refine ⟨3, residualCycleObservation_eq_of_choice_and_item hn P v hleave 3 _ _ hxy ?_ rfl⟩
      exact Finset.pair_comm _ _
    · refine ⟨5, residualCycleObservation_eq_of_choice_and_item hn P v hleave 5 _ _ hxy ?_ rfl⟩
      exact Finset.pair_comm _ _
    · refine ⟨7, residualCycleObservation_eq_of_choice_and_item hn P v hleave 7 _ _ hxy ?_ rfl⟩
      exact Finset.pair_comm _ _

private theorem residualCycleWalk_covers_observation
    (x y : Fin n) (hxy : x ≠ y) (r : Fin 4)
    (hpair : s(x, y) = s(v r, v (TrianglePacking.fourCycleNext r))) :
    (F hn).observationEdge ⟨pair n hxy, ⟨x, mem_pair_left n hxy⟩⟩ ∈
      (residualCycleWalk hn P v hleave).edges.toFinset := by
  obtain ⟨e, he⟩ := exists_residualCycleObservation_eq_pair hn P v hleave x y hxy r hpair
  rw [← he, observationEdge_residualCycleObservation_eq_edgeAt]
  apply List.mem_toFinset.mpr
  exact List.get_mem _ _

private theorem nearCycleObservation_ne_residualCycleObservation
    (t : P.Triangle) (e : Fin 6) (f : Fin 8) :
    nearCycleObservation hn P t e ≠ residualCycleObservation hn P v hleave f := by
  intro h
  have hchoice : nearEdgeChoice P t (nearCycleEdge e) =
      residualChoice P v hleave (residualObservationChoiceIndex f) := by
    rw [← nearCycleObservation_choice_eq_edgeChoice hn P t e,
      ← residualCycleObservation_choice_eq hn P v hleave f]
    exact congrArg Sigma.fst h
  let r : Fin 4 := residualObservationChoiceIndex f
  let a : Fin n := v r
  let b : Fin n := v (TrianglePacking.fourCycleNext r)
  have hab : a ≠ b := residualVertex_ne_next P v hleave r
  have ha : a ∈ (nearEdgeChoice P t (nearCycleEdge e) : Finset (Fin n)) := by
    rw [hchoice]
    change v r ∈ ({v r, v (TrianglePacking.fourCycleNext r)} : Finset (Fin n))
    simp
  have hb : b ∈ (nearEdgeChoice P t (nearCycleEdge e) : Finset (Fin n)) := by
    rw [hchoice]
    change v (TrianglePacking.fourCycleNext r) ∈
      ({v r, v (TrianglePacking.fourCycleNext r)} : Finset (Fin n))
    simp
  have hcover : P.CoversPair a b :=
    ⟨t, nearMemEdgeChoice_vertex P t (nearCycleEdge e) a ha,
      nearMemEdgeChoice_vertex P t (nearCycleEdge e) b hb⟩
  have hnotcover : ¬ P.CoversPair a b := by
    intro hcovered
    have hnotcycle := (hleave.2 a b hab).mp hcovered
    exact hnotcycle ⟨r, rfl⟩
  exact hnotcover hcover

private def residualEdgePositionObservation (e : Fin 8) : Fin 8 :=
  ⟨(e.1 + 1) % 8, Nat.mod_lt _ (by decide)⟩

private theorem residualCycleObservationPosition_edgePositionObservation (e : Fin 8) :
    residualCycleObservationPosition (residualEdgePositionObservation e) = e := by
  fin_cases e <;> rfl

private theorem residualCycleWalk_disjoint_nearTriangleCyclePacking :
    Disjoint (residualCycleWalk hn P v hleave).edges.toFinset
      (nearTriangleCyclePacking hn P).usedEdges := by
  apply Finset.disjoint_left.2
  intro edge hedgeResidual hedgeTriangle
  let positionResidual : Fin 8 :=
    (AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
      (residualCycleWalk_isCycle hn P v hleave)).symm ⟨edge, hedgeResidual⟩
  have hpositionResidual :
      AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (residualCycleWalk hn P v hleave)
        positionResidual = edge := by
    change ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
      (residualCycleWalk_isCycle hn P v hleave) positionResidual).1) = edge
    exact congrArg Subtype.val
      ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (residualCycleWalk_isCycle hn P v hleave)).apply_symm_apply ⟨edge, hedgeResidual⟩)
  obtain ⟨t, _, hedgeT⟩ := Finset.mem_biUnion.mp hedgeTriangle
  let positionT : Fin 6 :=
    (AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
      (nearTriangleCycleWalk_isCycle hn P t)).symm ⟨edge, hedgeT⟩
  have hpositionT :
      AppliedModelingLib.Foundations.Graph.simpleCycleEdgeAt (nearTriangleCycleWalk hn P t)
        positionT = edge := by
    change ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
      (nearTriangleCycleWalk_isCycle hn P t) positionT).1) = edge
    exact congrArg Subtype.val
      ((AppliedModelingLib.Foundations.Graph.simpleCycleEdgePositionEquiv
        (nearTriangleCycleWalk_isCycle hn P t)).apply_symm_apply ⟨edge, hedgeT⟩)
  have hobsResidual :
      (F hn).observationEdge
        (residualCycleObservation hn P v hleave
          (residualEdgePositionObservation positionResidual)) = edge := by
    rw [observationEdge_residualCycleObservation_eq_edgeAt,
      residualCycleObservationPosition_edgePositionObservation]
    exact hpositionResidual
  have hobsT :
      (F hn).observationEdge
        (nearCycleObservation hn P t (nearEdgePositionObservation positionT)) = edge := by
    rw [observationEdge_nearCycleObservation_eq_edgeAt,
      nearCycleObservationPosition_edgePositionObservation]
    exact hpositionT
  have hobs : nearCycleObservation hn P t (nearEdgePositionObservation positionT) =
      residualCycleObservation hn P v hleave
        (residualEdgePositionObservation positionResidual) :=
    (F hn).observationEdge_injective (hobsT.trans hobsResidual.symm)
  exact nearCycleObservation_ne_residualCycleObservation hn P v hleave t
    (nearEdgePositionObservation positionT)
    (residualEdgePositionObservation positionResidual) hobs

/-- The six-cycles induced by the packing, together with the leave's one
eight-cycle, form the concrete all-pairs incidence-cycle packing. -/
private noncomputable def allPairsNearPacking :
    PartialSimpleCyclePacking (F hn).incidenceGraph 8 :=
  PartialSimpleCyclePacking.cons (residualCycleWalk hn P v hleave)
    (residualCycleWalk_isCycle hn P v hleave) (by
      change 8 ≤ 8
      norm_num)
    ((nearTriangleCyclePacking hn P).relaxLength (by norm_num)) (by
      rw [PartialSimpleCyclePacking.usedEdges_relaxLength]
      exact residualCycleWalk_disjoint_nearTriangleCyclePacking hn P v hleave)

private theorem allPairsNearPacking_usedEdges :
    (allPairsNearPacking hn P v hleave).usedEdges =
      (residualCycleWalk hn P v hleave).edges.toFinset ∪
        (nearTriangleCyclePacking hn P).usedEdges := by
  unfold allPairsNearPacking
  rw [PartialSimpleCyclePacking.usedEdges_cons,
    PartialSimpleCyclePacking.usedEdges_relaxLength]

private theorem allPairsNearPacking_mem_of_nearTriangle
    {edge : Sym2 (Sum (Fin n) (ChoiceSet n))}
    (hedge : edge ∈ (nearTriangleCyclePacking hn P).usedEdges) :
    edge ∈ (allPairsNearPacking hn P v hleave).usedEdges := by
  rw [allPairsNearPacking_usedEdges]
  exact Finset.mem_union_right _ hedge

private theorem allPairsNearPacking_mem_of_residual
    {edge : Sym2 (Sum (Fin n) (ChoiceSet n))}
    (hedge : edge ∈ (residualCycleWalk hn P v hleave).edges.toFinset) :
    edge ∈ (allPairsNearPacking hn P v hleave).usedEdges := by
  rw [allPairsNearPacking_usedEdges]
  exact Finset.mem_union_left _ hedge

private theorem pairObservation_eq_of_members
    (C : ChoiceSet n) (x : {z : Fin n // z ∈ (F hn).members C})
    (u v : Fin n) (huv : u ≠ v) (hC : C = pair n huv) (hx : x.1 = u) :
    (⟨pair n huv, ⟨u, mem_pair_left n huv⟩⟩ : (F hn).Observation) = ⟨C, x⟩ := by
  refine Sigma.ext hC.symm ?_
  apply (Subtype.heq_iff_coe_eq (fun candidate => by simp [hC])).mpr
  exact hx.symm

private theorem allPairsNearPacking_covers_observation
    (C : ChoiceSet n) (x : {z : Fin n // z ∈ (F hn).members C}) :
    (F hn).observationEdge ⟨C, x⟩ ∈ (allPairsNearPacking hn P v hleave).usedEdges := by
  obtain ⟨u, w, huw, hCval⟩ := Finset.card_eq_two.mp C.2
  have hxmem : x.1 ∈ (C.1 : Finset (Fin n)) := x.2
  rw [hCval] at hxmem
  have hC : C = pair n huw := by
    apply Subtype.ext
    simpa [pair] using hCval
  have hxuw : x.1 = u ∨ x.1 = w := by
    change x.1 ∈ insert u ({w} : Finset (Fin n)) at hxmem
    rcases Finset.mem_insert.mp hxmem with hxu | hxw
    · exact Or.inl hxu
    · exact Or.inr (Finset.mem_singleton.mp hxw)
  rcases hxuw with hxu | hxw
  · by_cases hcover : P.CoversPair u w
    · have hnear := nearTriangleCyclePacking_covers_observation hn P u w huw hcover
      have hall := allPairsNearPacking_mem_of_nearTriangle hn P v hleave hnear
      rw [pairObservation_eq_of_members hn C x u w huw hC hxu] at hall
      exact hall
    · have hcycle : ∃ r : Fin 4, s(u, w) =
          s(v r, v (TrianglePacking.fourCycleNext r)) := by
        by_contra hnotcycle
        exact hcover ((hleave.2 u w huw).mpr hnotcycle)
      obtain ⟨r, hr⟩ := hcycle
      have hresidual := residualCycleWalk_covers_observation hn P v hleave u w huw r hr
      have hall := allPairsNearPacking_mem_of_residual hn P v hleave hresidual
      rw [pairObservation_eq_of_members hn C x u w huw hC hxu] at hall
      exact hall
  · have hwu : w ≠ u := Ne.symm huw
    have hC' : C = pair n hwu := by
      apply Subtype.ext
      change C.1 = ({w, u} : Finset (Fin n))
      rw [hCval]
      exact Finset.pair_comm _ _
    by_cases hcover : P.CoversPair w u
    · have hnear := nearTriangleCyclePacking_covers_observation hn P w u hwu hcover
      have hall := allPairsNearPacking_mem_of_nearTriangle hn P v hleave hnear
      rw [pairObservation_eq_of_members hn C x w u hwu hC' hxw] at hall
      exact hall
    · have hcycle : ∃ r : Fin 4, s(w, u) =
          s(v r, v (TrianglePacking.fourCycleNext r)) := by
        by_contra hnotcycle
        exact hcover ((hleave.2 w u hwu).mpr hnotcycle)
      obtain ⟨r, hr⟩ := hcycle
      have hresidual := residualCycleWalk_covers_observation hn P v hleave w u hwu r hr
      have hall := allPairsNearPacking_mem_of_residual hn P v hleave hresidual
      rw [pairObservation_eq_of_members hn C x w u hwu hC' hxw] at hall
      exact hall

private theorem allPairsNearPacking_isComplete :
    (allPairsNearPacking hn P v hleave).IsComplete := by
  unfold PartialSimpleCyclePacking.IsComplete
  apply Set.Subset.antisymm
  · intro edge hedge
    rw [← SimpleGraph.coe_edgeFinset]
    exact (allPairsNearPacking hn P v hleave).usedEdges_subset_edgeFinset hedge
  · intro edge hedge
    obtain ⟨o, ho⟩ := (F hn).observationEdge_surjective_edgeSet ⟨edge, hedge⟩
    rcases o with ⟨C, x⟩
    have hused := allPairsNearPacking_covers_observation hn P v hleave C x
    change (F hn).observationEdge ⟨C, x⟩ = edge at ho
    change edge ∈ (allPairsNearPacking hn P v hleave).usedEdges
    rw [← ho]
    exact hused

/-- A triangle packing whose leave is a four-cycle yields the all-pairs
signed cycle decomposition used in the paper's testing construction.  The
packed triangles give six-cycles, while the leave gives the one eight-cycle. -/
noncomputable def cycleDecompositionOfFourCycleLeave :
    ChoiceSystem.CycleDecomposition (F hn) :=
  (F hn).cycleDecompositionOfCompletePacking (allPairsNearPacking hn P v hleave)
    (allPairsNearPacking_isComplete hn P v hleave)

/-- The concrete graph traversals supply the alternating-cycle witness for
the decomposition arising from a four-cycle leave. -/
noncomputable def cycleDecompositionOfFourCycleLeave_alternatingCycleWitness :
    (cycleDecompositionOfFourCycleLeave hn P v hleave).AlternatingCycleWitness :=
  (F hn).cycleDecompositionOfCompletePacking_alternatingCycleWitness
    (allPairsNearPacking hn P v hleave) (allPairsNearPacking_isComplete hn P v hleave)

/-- The four-cycle-leave construction has no cycle longer than eight
incidences. -/
theorem cycleDecompositionOfFourCycleLeave_cycleMean_le_eight :
    (cycleDecompositionOfFourCycleLeave hn P v hleave).cycleMean ≤ 8 := by
  apply (cycleDecompositionOfFourCycleLeave hn P v hleave).cycleMean_le_of_forall_length_le 8
  intro cycle
  change ((F hn).cycleDecompositionOfCompletePacking
    (allPairsNearPacking hn P v hleave)
    (allPairsNearPacking_isComplete hn P v hleave)).length cycle ≤ 8
  rw [ChoiceFrame.cycleDecompositionOfCompletePacking_length]
  exact (allPairsNearPacking hn P v hleave).length_le cycle

/-- The corresponding source dispersion statistic is also bounded by eight. -/
theorem cycleDecompositionOfFourCycleLeave_cycleDispersion_le_eight :
    CycleMixture.cycleDispersion (F hn).incidenceCount
      (cycleDecompositionOfFourCycleLeave hn P v hleave).length ≤ 8 := by
  apply (cycleDecompositionOfFourCycleLeave hn P v hleave).cycleDispersion_le_of_forall_length_le 8
  intro cycle
  change ((F hn).cycleDecompositionOfCompletePacking
    (allPairsNearPacking hn P v hleave)
    (allPairsNearPacking_isComplete hn P v hleave)).length cycle ≤ 8
  rw [ChoiceFrame.cycleDecompositionOfCompletePacking_length]
  exact (allPairsNearPacking hn P v hleave).length_le cycle

private theorem cycleDecompositionOfFourCycleLeave_length_none :
    (cycleDecompositionOfFourCycleLeave hn P v hleave).length
      (none : Option P.Triangle) = 8 := by
  change ((F hn).cycleDecompositionOfCompletePacking
    (allPairsNearPacking hn P v hleave)
    (allPairsNearPacking_isComplete hn P v hleave)).length none = 8
  rw [ChoiceFrame.cycleDecompositionOfCompletePacking_length]
  rfl

private theorem cycleDecompositionOfFourCycleLeave_length_some
    (t : ((nearTriangleCyclePacking hn P).relaxLength (by norm_num)).Cycle) :
    (cycleDecompositionOfFourCycleLeave hn P v hleave).length (some t) = 6 := by
  change ((F hn).cycleDecompositionOfCompletePacking
    (allPairsNearPacking hn P v hleave)
    (allPairsNearPacking_isComplete hn P v hleave)).length (some t) = 6
  rw [ChoiceFrame.cycleDecompositionOfCompletePacking_length]
  rfl

private theorem cycleDecompositionOfFourCycleLeave_length_cycle
    (cycle : (allPairsNearPacking hn P v hleave).Cycle) :
    (cycleDecompositionOfFourCycleLeave hn P v hleave).length cycle =
      match cycle with
      | none => 8
      | some _ => 6 := by
  cases cycle with
  | none => exact cycleDecompositionOfFourCycleLeave_length_none hn P v hleave
  | some t =>
    change ((F hn).cycleDecompositionOfCompletePacking
      (allPairsNearPacking hn P v hleave)
      (allPairsNearPacking_isComplete hn P v hleave)).length (some t) = 6
    rw [ChoiceFrame.cycleDecompositionOfCompletePacking_length]
    rfl

private theorem cycleDecompositionOfFourCycleLeave_sum_length_sq :
    (∑ cycle : (cycleDecompositionOfFourCycleLeave hn P v hleave).Cycle,
      ((cycleDecompositionOfFourCycleLeave hn P v hleave).length cycle : ℝ) ^ 2) =
      6 * (∑ cycle : (cycleDecompositionOfFourCycleLeave hn P v hleave).Cycle,
        ((cycleDecompositionOfFourCycleLeave hn P v hleave).length cycle : ℝ)) + 16 := by
  change (∑ cycle : Option P.Triangle,
    ((cycleDecompositionOfFourCycleLeave hn P v hleave).length cycle : ℝ) ^ 2) =
      6 * (∑ cycle : Option P.Triangle,
        ((cycleDecompositionOfFourCycleLeave hn P v hleave).length cycle : ℝ)) + 16
  rw [Fintype.sum_option, Fintype.sum_option]
  rw [cycleDecompositionOfFourCycleLeave_length_none]
  simp_rw [cycleDecompositionOfFourCycleLeave_length_cycle]
  norm_num
  ring

private theorem cycleDecompositionOfFourCycleLeave_sum_length_sq_eq :
    (∑ cycle : (cycleDecompositionOfFourCycleLeave hn P v hleave).Cycle,
      ((cycleDecompositionOfFourCycleLeave hn P v hleave).length cycle : ℝ) ^ 2) =
      6 * ((F hn).incidenceCount : ℝ) + 16 := by
  rw [cycleDecompositionOfFourCycleLeave_sum_length_sq]
  rw [show (∑ cycle : (cycleDecompositionOfFourCycleLeave hn P v hleave).Cycle,
      ((cycleDecompositionOfFourCycleLeave hn P v hleave).length cycle : ℝ)) =
      ((F hn).incidenceCount : ℝ) by
    exact_mod_cast (F hn).cycleDecompositionOfCompletePacking_total_length
      (allPairsNearPacking hn P v hleave) (allPairsNearPacking_isComplete hn P v hleave)]

/-- In the `6m+5` all-pairs construction, all packed triangles have length
six and the only exceptional cycle has length eight.  Thus the source's
dispersion statistic is exactly `6 + 16 / d`. -/
theorem cycleDecompositionOfFourCycleLeave_cycleDispersion_eq_six_add_sixteen_div :
    CycleMixture.cycleDispersion (F hn).incidenceCount
      (cycleDecompositionOfFourCycleLeave hn P v hleave).length =
      6 + 16 / ((F hn).incidenceCount : ℝ) := by
  unfold CycleMixture.cycleDispersion
  rw [cycleDecompositionOfFourCycleLeave_sum_length_sq_eq]
  have hd : ((F hn).incidenceCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (F hn).incidenceCount_pos
  field_simp

private theorem riskLower_antitone_exponent {a b : ℝ} (hab : a ≤ b) :
    1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) := by
  have hexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hsqrt : Real.sqrt (Real.exp a - 1) ≤ Real.sqrt (Real.exp b - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- The all-pairs testing lower bound from the `n = 6m + 5` construction.
The triangle packing contributes six-cycles and its four-cycle leave contributes
one eight-cycle, so both cycle statistics needed by Theorem 1 are at most eight. -/
theorem productTestingLowerBound_ofFourCycleLeave
    (hleave : P.LeavesFourCycle v)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hsmall : 16 * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame n hn) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (8 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            ((frame n hn).incidenceCount : ℝ)) - 1)) := by
  let D := cycleDecompositionOfFourCycleLeave hn P v hleave
  let W : D.AlternatingCycleWitness := by
    simpa [D] using
      cycleDecompositionOfFourCycleLeave_alternatingCycleWitness hn P v hleave
  let d : ℝ := ((frame n hn).incidenceCount : ℝ)
  have hmean : D.cycleMean ≤ 8 := by
    simpa [D] using cycleDecompositionOfFourCycleLeave_cycleMean_le_eight hn P v hleave
  have hdispersion :
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length ≤ 8 := by
    simpa [D] using
      cycleDecompositionOfFourCycleLeave_cycleDispersion_le_eight hn P v hleave
  have hsmallD : 2 * D.cycleMean * δ ≤ 1 := by
    calc
      2 * D.cycleMean * δ = D.cycleMean * (2 * δ) := by ring
      _ ≤ 8 * (2 * δ) :=
        mul_le_mul_of_nonneg_right hmean (by positivity)
      _ = 16 * δ := by ring
      _ ≤ 1 := hsmall
  have hbase := D.theorem1_productTestingLowerBound W δ hδ_nonneg hsmallD N
  let a : ℝ :=
    (8 * D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length *
        (N : ℝ) ^ 2 * δ ^ 4) / d
  let b : ℝ := (8 * (8 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d
  have hdispersion_nonneg : 0 ≤
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length := by
    unfold CycleMixture.cycleDispersion
    positivity
  have hmean_pow : D.cycleMean ^ 4 ≤ (8 : ℝ) ^ 4 :=
    pow_le_pow_left₀ D.cycleMean_pos.le hmean 4
  have hproduct : D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length ≤ (8 : ℝ) ^ 5 := by
    calc
      D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length ≤
          (8 : ℝ) ^ 4 *
            CycleMixture.cycleDispersion (frame n hn).incidenceCount D.length :=
        mul_le_mul_of_nonneg_right hmean_pow hdispersion_nonneg
      _ ≤ (8 : ℝ) ^ 4 * 8 :=
        mul_le_mul_of_nonneg_left hdispersion (pow_nonneg (by norm_num) 4)
      _ = (8 : ℝ) ^ 5 := by ring
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
      _ ≤ (8 : ℝ) ^ 5 * (8 * (N : ℝ) ^ 2 * δ ^ 4) / d :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hproduct hfactor) hdpos.le
      _ = (8 * (8 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
  have hlower :
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
        1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) :=
    riskLower_antitone_exponent hab
  intro φ
  obtain ⟨q, hseparated, herror⟩ := hbase φ
  refine ⟨q, hseparated, ?_⟩
  apply hlower.trans
  simpa [a, d] using herror

/-- The same `n = 6m + 5` all-pairs lower bound with the exact incidence
count `d = n(n-1)` substituted in the denominator. -/
theorem productTestingLowerBound_ofFourCycleLeave_mul_pred
    (hleave : P.LeavesFourCycle v)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hsmall : 16 * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame n hn) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (8 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            ((n * (n - 1) : ℕ) : ℝ)) - 1)) := by
  simpa only [incidenceCount_eq_mul_pred] using
    productTestingLowerBound_ofFourCycleLeave hn P v hleave δ hδ_nonneg hsmall N

/-- The paper's all-pairs lower bound for every cardinality `n = 6m + 5`.
The packing is the concrete Feder--Subi construction in the combinatorics
library, so no triangle-design existence hypothesis remains at this boundary. -/
theorem productTestingLowerBound_of_six_mul_add_five
    (m : ℕ) (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hsmall : 16 * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame (6 * m + 5) (by omega)) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (8 : ℝ) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            (((6 * m + 5) * (6 * m + 5 - 1) : ℕ) : ℝ)) - 1)) := by
  let hn : 2 ≤ 6 * m + 5 := by omega
  obtain ⟨P, v, hleave⟩ :=
    TrianglePacking.exists_federSubiPackingFin_leavesFourCycle m
  simpa only using
    productTestingLowerBound_ofFourCycleLeave_mul_pred hn P v hleave δ hδ_nonneg hsmall N

end TriangleCycles

end NearPackingBridge

end AllPairs

end SeshadriUgander2020IIATesting
