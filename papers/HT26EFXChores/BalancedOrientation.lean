import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators

/-!
# Balanced Endpoint Orientations

The paper's balanced-orientation lemma is implemented through Hall's marriage
theorem.  A vertex with quota `q` is replaced by `q` distinguishable slots;
Hall matches those slots injectively to incident edges.  Turning that matching
into an `Option`-valued owner map also gives the partial-orientation clause.

Source: `EFXadditivechores.tex`, lines 1019--1034.
-/

open scoped BigOperators

namespace HT26EFXChores

open Finset

private theorem assignmentSlotsExist
    (Vertex Edge : Type) [Fintype Vertex] [DecidableEq Vertex] [DecidableEq Edge]
    (edges : Finset Edge) (endpoints : Edge → Finset Vertex) (quota : Vertex → ℕ)
    (hcondition : ∀ vertices : Finset Vertex,
      vertices.sum quota ≤ (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card) :
    ∃ f : (Σ vertex : Vertex, Fin (quota vertex)) → { edge // edge ∈ edges },
      Function.Injective f ∧ ∀ slot, slot.1 ∈ endpoints (f slot).1 := by
  let Slot := Σ vertex : Vertex, Fin (quota vertex)
  let EdgeIn := { edge // edge ∈ edges }
  let related : Slot → EdgeIn → Prop := fun slot edge => slot.1 ∈ endpoints edge.1
  have hhall : ∀ slots : Finset Slot,
      slots.card ≤ #{edge : EdgeIn | ∃ slot ∈ slots, related slot edge} := by
    intro slots
    let vertices : Finset Vertex := slots.image Sigma.fst
    have hslots : slots.card ≤ vertices.sum quota := by
      let capacity : Finset Slot := vertices.sigma fun vertex => Finset.univ
      have hsubset : slots ⊆ capacity := by
        intro slot hslot
        apply Finset.mem_sigma.mpr
        exact ⟨Finset.mem_image.mpr ⟨slot, hslot, rfl⟩, Finset.mem_univ _⟩
      calc
        slots.card ≤ capacity.card := Finset.card_le_card hsubset
        _ = vertices.sum quota := by
          change (vertices.sigma fun vertex => Finset.univ).card = vertices.sum quota
          rw [Finset.card_sigma]
          simp
    have hincident :
        #{edge : EdgeIn | ∃ slot ∈ slots, related slot edge} =
          (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card := by
      change (edges.attach.filter fun edge : EdgeIn =>
        ∃ slot ∈ slots, related slot edge).card =
          (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card
      rw [Finset.filter_attach']
      simp only [Finset.card_map]
      rw [Finset.card_attach]
      apply congrArg Finset.card
      ext edge
      simp only [Finset.mem_filter, related, vertices]
      constructor
      · rintro ⟨hedge, hsubtype, slot, hslot, hendpoint⟩
        refine ⟨hedge, slot.1, ?_⟩
        exact Finset.mem_inter.mpr
          ⟨hendpoint, Finset.mem_image.mpr ⟨slot, hslot, rfl⟩⟩
      · rintro ⟨hedge, vertex, hintersection⟩
        rcases Finset.mem_inter.mp hintersection with ⟨hendpoint, hvertex⟩
        rcases Finset.mem_image.mp hvertex with ⟨slot, hslot, hslotVertex⟩
        refine ⟨hedge, hedge, slot, hslot, ?_⟩
        simpa [hslotVertex] using hendpoint
    calc
      slots.card ≤ vertices.sum quota := hslots
      _ ≤ (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card :=
        hcondition vertices
      _ = #{edge : EdgeIn | ∃ slot ∈ slots, related slot edge} := hincident.symm
  obtain ⟨f, hinjective, hf⟩ :=
    Fintype.all_card_le_filter_rel_iff_exists_injective related |>.mp hhall
  exact ⟨f, hinjective, hf⟩

private theorem ownerOfInjectiveSlots
    (Vertex Edge : Type) [Fintype Vertex] [DecidableEq Vertex] [DecidableEq Edge]
    (edges : Finset Edge) (endpoints : Edge → Finset Vertex) (quota : Vertex → ℕ)
    (f : (Σ vertex : Vertex, Fin (quota vertex)) → { edge // edge ∈ edges })
    (hinjective : Function.Injective f)
    (hendpoint : ∀ slot, slot.1 ∈ endpoints (f slot).1) :
    ∃ owner : Edge → Option Vertex,
      (∀ edge ∈ edges, ∀ vertex, owner edge = some vertex → vertex ∈ endpoints edge) ∧
        (∀ vertex, (edges.filter fun edge => owner edge = some vertex).card = quota vertex) ∧
          ∀ slot, owner (f slot).1 = some slot.1 := by
  classical
  let owner : Edge → Option Vertex := fun edge =>
    if hedge : edge ∈ edges then
      if hslot : ∃ slot, f slot = ⟨edge, hedge⟩ then some (Classical.choose hslot).1 else none
    else none
  have howner_f : ∀ slot, owner (f slot).1 = some slot.1 := by
    intro slot
    have hexists : ∃ candidate, f candidate = f slot := ⟨slot, rfl⟩
    simp only [owner, dif_pos (f slot).2]
    rw [dif_pos hexists]
    congr 1
    have hchoice : f (Classical.choose hexists) = f slot :=
      Classical.choose_spec hexists
    exact congrArg Sigma.fst (hinjective hchoice)
  have howner_mem : ∀ edge (hedge : edge ∈ edges) vertex,
      owner edge = some vertex → vertex ∈ endpoints edge := by
    intro edge hedge vertex howner
    simp only [owner, dif_pos hedge] at howner
    split at howner
    · rename_i hslot
      have hchoice := Classical.choose_spec hslot
      have hvalue : (Classical.choose hslot).1 = vertex := by
        simpa using Option.some.inj howner
      simpa [hchoice, hvalue] using hendpoint (Classical.choose hslot)
    · simp_all
  have howner_iff : ∀ slot vertex,
      owner (f slot).1 = some vertex ↔ slot.1 = vertex := by
    intro slot vertex
    constructor
    · intro howner
      rw [howner_f slot] at howner
      exact Option.some.inj howner
    · intro hslot
      simpa [hslot] using howner_f slot
  refine ⟨owner, ?_, ?_, howner_f⟩
  · exact howner_mem
  · intro vertex
    let slotsAt : Finset (Σ vertex : Vertex, Fin (quota vertex)) :=
      (Finset.univ : Finset (Fin (quota vertex))).map
        ⟨fun index => Sigma.mk vertex index, by
          intro first second heq
          exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2⟩
    have hslotsAt : slotsAt = (Finset.univ.filter fun slot => slot.1 = vertex) := by
      ext slot
      simp only [slotsAt, Finset.mem_map, Finset.mem_univ, true_and,
        Finset.mem_filter]
      constructor
      · rintro ⟨index, hequality⟩
        exact (congrArg Sigma.fst hequality).symm
      · intro hslot
        rcases slot with ⟨slotVertex, index⟩
        change slotVertex = vertex at hslot
        subst slotVertex
        exact ⟨index, rfl⟩
    have hcard_slotsAt : slotsAt.card = quota vertex := by
      simp [slotsAt]
    let embedFiltered : { edge // edge ∈ edges.filter fun edge => owner edge = some vertex } ↪
        { edge // edge ∈ edges } :=
      ⟨fun edge => ⟨edge.1, (Finset.mem_filter.mp edge.2).1⟩, by
        intro first second heq
        apply Subtype.ext
        simpa using congrArg Subtype.val heq⟩
    have himage :
        ((edges.filter fun edge => owner edge = some vertex).attach).map embedFiltered =
          slotsAt.image f := by
      ext edge
      constructor
      · intro hedge
        simp only [Finset.mem_map, Finset.mem_attach] at hedge
        obtain ⟨edge', hedge', hvalue⟩ := hedge
        have howner := (Finset.mem_filter.mp edge'.2).1
        have hassigned := (Finset.mem_filter.mp edge'.2).2
        have hslot : ∃ slot, f slot = ⟨edge'.1, howner⟩ := by
          simp only [owner, dif_pos howner] at hassigned
          split at hassigned
          · exact ‹∃ slot, f slot = ⟨edge'.1, howner⟩›
          · simp_all
        obtain ⟨slot, hslot⟩ := hslot
        have hslotVertex : slot.1 = vertex := by
          apply (howner_iff slot vertex).mp
          simpa [hslot] using hassigned
        have hslotMem : slot ∈ slotsAt := by simpa [hslotsAt] using hslotVertex
        simp only [Finset.mem_image]
        refine ⟨slot, hslotMem, ?_⟩
        calc
          f slot = ⟨edge'.1, howner⟩ := hslot
          _ = embedFiltered edge' := by apply Subtype.ext; rfl
          _ = edge := hvalue
      · intro hedge
        simp only [Finset.mem_image] at hedge
        obtain ⟨slot, hslot, hslotEdge⟩ := hedge
        have hslotVertex : slot.1 = vertex := by simpa [hslotsAt] using hslot
        have howner : owner (f slot).1 = some vertex := by
          rw [← hslotVertex]
          exact howner_f slot
        have hfilter : (f slot).1 ∈ edges.filter fun edge => owner edge = some vertex :=
          Finset.mem_filter.mpr ⟨(f slot).2, howner⟩
        simp only [Finset.mem_map, Finset.mem_attach]
        refine ⟨⟨(f slot).1, hfilter⟩, True.intro, ?_⟩
        calc
          embedFiltered ⟨(f slot).1, hfilter⟩ = f slot := by
            apply Subtype.ext
            rfl
          _ = edge := hslotEdge
    calc
      (edges.filter fun edge => owner edge = some vertex).card =
          (((edges.filter fun edge => owner edge = some vertex).attach).map embedFiltered).card := by
        simp
      _ = (slotsAt.image f).card := congrArg Finset.card himage
      _ = slotsAt.card := Finset.card_image_iff.mpr hinjective.injOn
      _ = quota vertex := hcard_slotsAt

/-- The partial assignment clause of the paper's balanced-orientation lemma. -/
theorem partialBalancedOrientation
    (Vertex Edge : Type) [Fintype Vertex] [DecidableEq Vertex] [DecidableEq Edge]
    (edges : Finset Edge) (endpoints : Edge → Finset Vertex) (quota : Vertex → ℕ)
    (hcondition : ∀ vertices : Finset Vertex,
      vertices.sum quota ≤ (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card) :
    ∃ owner : Edge → Option Vertex,
      (∀ edge ∈ edges, ∀ vertex, owner edge = some vertex → vertex ∈ endpoints edge) ∧
        ∀ vertex, (edges.filter fun edge => owner edge = some vertex).card = quota vertex := by
  obtain ⟨f, hinjective, hendpoint⟩ :=
    assignmentSlotsExist Vertex Edge edges endpoints quota hcondition
  obtain ⟨owner, hmem, hcard, _⟩ :=
    ownerOfInjectiveSlots Vertex Edge edges endpoints quota f hinjective hendpoint
  exact ⟨owner, hmem, hcard⟩

/-- The full endpoint-assignment equivalence in the paper's orientation lemma. -/
theorem balancedOrientationIff
    (Vertex Edge : Type) [Fintype Vertex] [DecidableEq Vertex] [DecidableEq Edge]
    (edges : Finset Edge) (endpoints : Edge → Finset Vertex) (quota : Vertex → ℕ)
    (hends : ∀ edge ∈ edges, (endpoints edge).card = 2)
    (hsum : Finset.univ.sum quota = edges.card) :
    (∃ owner : Edge → Option Vertex,
      (∀ edge ∈ edges, ∃ vertex, owner edge = some vertex ∧ vertex ∈ endpoints edge) ∧
        ∀ vertex, (edges.filter fun edge => owner edge = some vertex).card = quota vertex) ↔
      ∀ vertices : Finset Vertex,
        vertices.sum quota ≤ (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card := by
  constructor
  · rintro ⟨owner, howner, hcard⟩ vertices
    let assigned : Vertex → Finset Edge := fun vertex =>
      edges.filter fun edge => owner edge = some vertex
    have hdisjoint : (vertices : Set Vertex).PairwiseDisjoint assigned := by
      intro first hfirst second hsecond hne
      change Disjoint (assigned first) (assigned second)
      rw [Finset.disjoint_left]
      intro edge hfirstEdge hsecondEdge
      have hfirstOwner : owner edge = some first :=
        (Finset.mem_filter.mp hfirstEdge).2
      have hsecondOwner : owner edge = some second :=
        (Finset.mem_filter.mp hsecondEdge).2
      exact hne (Option.some.inj (hfirstOwner.symm.trans hsecondOwner))
    calc
      vertices.sum quota = ∑ vertex ∈ vertices, (assigned vertex).card := by
        apply Finset.sum_congr rfl
        intro vertex hvertex
        exact (hcard vertex).symm
      _ = (vertices.biUnion assigned).card := (Finset.card_biUnion hdisjoint).symm
      _ ≤ (edges.filter fun edge => (endpoints edge ∩ vertices).Nonempty).card := by
        apply Finset.card_le_card
        intro edge hedge
        obtain ⟨vertex, hvertex, hassigned⟩ := Finset.mem_biUnion.mp hedge
        have hedgeMem : edge ∈ edges := (Finset.mem_filter.mp hassigned).1
        have hownerEq : owner edge = some vertex := (Finset.mem_filter.mp hassigned).2
        obtain ⟨ownerVertex, hownerEq', hendpoint⟩ := howner edge hedgeMem
        have hvertexEndpoint : vertex ∈ endpoints edge := by
          have hvertices : ownerVertex = vertex :=
            Option.some.inj (hownerEq'.symm.trans hownerEq)
          simpa [hvertices] using hendpoint
        exact Finset.mem_filter.mpr ⟨hedgeMem,
          ⟨vertex, Finset.mem_inter.mpr ⟨hvertexEndpoint, hvertex⟩⟩⟩
  · intro hcondition
    obtain ⟨f, hinjective, hendpoint⟩ :=
      assignmentSlotsExist Vertex Edge edges endpoints quota hcondition
    have hslotCard : Fintype.card (Σ vertex : Vertex, Fin (quota vertex)) =
        Fintype.card { edge // edge ∈ edges } := by
      simpa using hsum
    have hsurjective : Function.Surjective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinjective, hslotCard⟩ |>.2
    obtain ⟨owner, hownerMem, hcard, hownerF⟩ :=
      ownerOfInjectiveSlots Vertex Edge edges endpoints quota f hinjective hendpoint
    refine ⟨owner, ?_, hcard⟩
    intro edge hedge
    obtain ⟨slot, hslot⟩ := hsurjective ⟨edge, hedge⟩
    refine ⟨slot.1, ?_, ?_⟩
    · simpa [hslot] using hownerF slot
    · simpa [hslot] using hendpoint slot

end HT26EFXChores
