import AppliedModelingLib.Foundations.Math.IntervalCrossing
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Order.ProjIcc

/-!
# Connected Covers

Connectedness consequences for finite relatively closed covers, including the
overlap-graph formulation used by finite-family support arguments. This layer
is separate from elementary real interval crossing so existing clients of the
latter do not inherit graph imports or unrelated container changes.
-/

namespace AppliedModelingLib

open Set

/--
A compact subset of the real line with no gap between any two of its points is
preconnected.  Compactness supplies the two endpoint points around a putative
missing value; the no-gap condition then rules that separation out.
-/
theorem isPreconnected_of_isCompact_of_exists_between
    {s : Set ℝ} (hcompact : IsCompact s)
    (hbetween : ∀ x ∈ s, ∀ y ∈ s, x < y →
      ∃ z ∈ s, x < z ∧ z < y) :
    IsPreconnected s := by
  rw [isPreconnected_iff_ordConnected]
  apply Set.ordConnected_of_Ioo
  intro x hx y hy hxy z hz
  by_contra hzS
  let left : Set ℝ := s ∩ Iic z
  let right : Set ℝ := s ∩ Ici z
  have hleft_compact : IsCompact left := hcompact.inter_right isClosed_Iic
  have hright_compact : IsCompact right := hcompact.inter_right isClosed_Ici
  have hleft_nonempty : left.Nonempty := ⟨x, hx, hz.1.le⟩
  have hright_nonempty : right.Nonempty := ⟨y, hy, hz.2.le⟩
  rcases hleft_compact.exists_isGreatest hleft_nonempty with ⟨u, hu⟩
  rcases hright_compact.exists_isLeast hright_nonempty with ⟨v, hv⟩
  have huz : u < z := by
    apply lt_of_le_of_ne hu.1.2
    intro huz
    apply hzS
    rw [← huz]
    exact hu.1.1
  have hzv : z < v := by
    apply lt_of_le_of_ne hv.1.2
    intro hvz
    apply hzS
    rw [hvz]
    exact hv.1.1
  obtain ⟨w, hw, huw, hwv⟩ := hbetween u hu.1.1 v hv.1.1 (huz.trans hzv)
  have hwz : w ≠ z := by
    intro hwz
    apply hzS
    rw [← hwz]
    exact hw
  rcases lt_or_gt_of_ne hwz with hwlt | hwgt
  · have hwu : w ≤ u := hu.2 ⟨hw, hwlt.le⟩
    exact (not_lt_of_ge hwu) huw
  · have hvw : v ≤ w := hv.2 ⟨hw, hwgt.le⟩
    exact (not_lt_of_ge hvw) hwv

/--
A compact subset of the real line that is not order-connected has a witnessed
open gap: the gap ends at a point of the set and there is a point of the set
weakly to its left.  This endpoint form is useful when a local gap deviation
must be applied at a represented support point.
-/
theorem exists_open_gap_of_isCompact_of_not_ordConnected
    {s : Set ℝ} (hcompact : IsCompact s) (hnot : ¬ Set.OrdConnected s) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ sᶜ ∧ b ∈ s ∧
      ∃ x ∈ s, x ≤ a := by
  rw [Set.ordConnected_iff] at hnot
  push Not at hnot
  obtain ⟨x, hx, y, hy, _, hnot_subset⟩ := hnot
  obtain ⟨z, hz, hzS⟩ := Set.not_subset.mp hnot_subset
  let left : Set ℝ := s ∩ Set.Iic z
  let right : Set ℝ := s ∩ Set.Ici z
  have hleft_compact : IsCompact left := hcompact.inter_right isClosed_Iic
  have hright_compact : IsCompact right := hcompact.inter_right isClosed_Ici
  have hleft_nonempty : left.Nonempty := ⟨x, hx, hz.1⟩
  have hright_nonempty : right.Nonempty := ⟨y, hy, hz.2⟩
  obtain ⟨a, ha⟩ := hleft_compact.exists_isGreatest hleft_nonempty
  obtain ⟨b, hb⟩ := hright_compact.exists_isLeast hright_nonempty
  have haz : a < z := by
    apply lt_of_le_of_ne ha.1.2
    intro haz
    apply hzS
    rw [← haz]
    exact ha.1.1
  have hzb : z < b := by
    apply lt_of_le_of_ne hb.1.2
    intro hzb
    apply hzS
    rw [hzb]
    exact hb.1.1
  refine ⟨a, b, haz.trans hzb, ?_, hb.1.1, a, ha.1.1, le_rfl⟩
  intro w hw hwS
  by_cases hwz : w ≤ z
  · have hwleft : w ∈ left := ⟨hwS, hwz⟩
    exact (not_lt_of_ge (ha.2 hwleft)) hw.1
  · have hzw : z < w := lt_of_not_ge hwz
    have hwright : w ∈ right := ⟨hwS, hzw.le⟩
    exact (not_lt_of_ge (hb.2 hwright)) hw.2

/--
A compact order-connected nonnegative subset of the real line that contains
the origin is a closed interval with left endpoint zero.  The right endpoint
is selected from the compact set itself, so this is suitable for passing from
a support no-gap theorem to a concrete interval domain.
-/
theorem exists_eq_Icc_of_isCompact_of_ordConnected_of_zero_mem_of_nonneg
    {s : Set ℝ} (hcompact : IsCompact s) (hconnected : Set.OrdConnected s)
    (hzero : 0 ∈ s) (hnonneg : ∀ x ∈ s, 0 ≤ x) :
    ∃ B : ℝ, 0 ≤ B ∧ s = Set.Icc 0 B := by
  obtain ⟨B, hB⟩ := hcompact.exists_isGreatest ⟨0, hzero⟩
  refine ⟨B, hnonneg B hB.1, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨hnonneg x hx, hB.2 hx⟩
  · exact hconnected.out hzero hB.1

/--
An injective compact planar support whose first projection is a nonempty
closed interval is the graph of a globally continuous function over that
interval.  The function is extended outside the interval by composing its
compact-graph parametrization with interval projection; its values on the
interval are exactly the represented support values.
-/
theorem exists_continuous_graph_of_isCompact_of_injOn_fst_of_fst_image_eq_Icc
    {S : Set (ℝ × ℝ)} {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact S)
    (hinj : S.InjOn Prod.fst) (himage : Prod.fst '' S = Set.Icc a b) :
    ∃ g : ℝ → ℝ, Continuous g ∧
      (∀ x ∈ Set.Icc a b, (x, g x) ∈ S) ∧
      (∀ z ∈ S, z.2 = g z.1) := by
  classical
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  let f : S → Set.Icc a b := fun z =>
    ⟨z.val.1, by
      rw [← himage]
      exact ⟨z.val, z.property, rfl⟩⟩
  have hf_cont : Continuous f := by
    exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hfst := congrArg Subtype.val hxy
    exact hinj x.property y.property (by simpa [f] using hfst)
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : x.val ∈ Prod.fst '' S := by
      rw [himage]
      exact x.property
    rcases hx with ⟨z, hz, hzx⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    simpa [f] using hzx
  let e : S ≃ Set.Icc a b := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hf_closedEmbedding : Topology.IsClosedEmbedding f := hf_cont.isClosedEmbedding hf_inj
  let eHomeo : S ≃ₜ Set.Icc a b :=
    e.toHomeomorphOfIsInducing (by simpa [e] using hf_closedEmbedding.isInducing)
  let gOn : Set.Icc a b → ℝ := fun x => (eHomeo.symm x).val.2
  have hgOn_cont : Continuous gOn :=
    (continuous_snd.comp continuous_subtype_val).comp eHomeo.symm.continuous
  let g : ℝ → ℝ := fun x => gOn (Set.projIcc a b hab x)
  have hg_cont : Continuous g := hgOn_cont.comp continuous_projIcc
  refine ⟨g, hg_cont, ?_, ?_⟩
  · intro x hx
    let x' : Set.Icc a b := ⟨x, hx⟩
    have hfst : (eHomeo.symm x').val.1 = x := by
      have heq : e (eHomeo.symm x') = x' := by
        simpa [eHomeo] using e.apply_symm_apply x'
      have heq_val := congrArg Subtype.val heq
      simpa [e, f] using heq_val
    have hg : g x = (eHomeo.symm x').val.2 := by
      dsimp [g]
      rw [Set.projIcc_of_mem hab hx]
    have hpair : (x, g x) = (eHomeo.symm x').val := by
      apply Prod.ext
      · exact hfst.symm
      · exact hg
    rw [hpair]
    exact (eHomeo.symm x').property
  · intro z hz
    have hzfst : z.1 ∈ Set.Icc a b := by
      rw [← himage]
      exact ⟨z, hz, rfl⟩
    have hzgraph : (z.1, g z.1) ∈ S := by
      exact (by
        let z' : Set.Icc a b := ⟨z.1, hzfst⟩
        have hfst : (eHomeo.symm z').val.1 = z.1 := by
          have heq : e (eHomeo.symm z') = z' := by
            simpa [eHomeo] using e.apply_symm_apply z'
          have heq_val := congrArg Subtype.val heq
          simpa [e, f] using heq_val
        have hg : g z.1 = (eHomeo.symm z').val.2 := by
          dsimp [g]
          rw [Set.projIcc_of_mem hab hzfst]
        have hpair : (z.1, g z.1) = (eHomeo.symm z').val := by
          apply Prod.ext
          · exact hfst.symm
          · exact hg
        rw [hpair]
        exact (eHomeo.symm z').property)
    have hEq : z = (z.1, g z.1) := hinj hz hzgraph rfl
    calc
      z.2 = (z.1, g z.1).2 := congrArg Prod.snd hEq
      _ = g z.1 := rfl

/--
On a preconnected set, a finite pairwise-disjoint family of relatively closed,
nonempty sets cannot cover the set unless it has a single index.  This is the
finite closed-cover form of connectedness used to turn a support interval into
an overlap-graph connectivity statement.
-/
theorem subsingleton_of_pairwiseDisjoint_closed_cover_of_isPreconnected
    {X ι : Type*} [TopologicalSpace X] [Finite ι] {s : Set X}
    (hs : IsPreconnected s) (A : ι → Set X)
    (hnonempty : ∀ i, (A i ∩ s).Nonempty)
    (hdisjoint : Pairwise fun i j => Disjoint (A i ∩ s) (A j ∩ s))
    (hclosed : ∀ i, IsClosed (A i ∩ s))
    (hcover : ⋃ i, A i ∩ s = s) :
    Subsingleton ι := by
  letI : PreconnectedSpace s := Subtype.preconnectedSpace hs
  let B : ι → Set s := fun i => Subtype.val ⁻¹' (A i ∩ s)
  have hB_nonempty : ∀ i, (B i).Nonempty := by
    intro i
    rcases hnonempty i with ⟨x, hx⟩
    exact ⟨⟨x, hx.2⟩, hx⟩
  have hB_disjoint : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.mp (hdisjoint hij) hxi hxj
  have hB_closed : ∀ i, IsClosed (B i) := by
    intro i
    change IsClosed (Subtype.val ⁻¹' (A i ∩ s))
    exact (hclosed i).preimage continuous_subtype_val
  have hB_cover : ⋃ i, B i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : (x : X) ∈ ⋃ i, A i ∩ s := by
      rw [hcover]
      exact x.property
    simpa [B] using hx
  exact subsingleton_of_disjoint_isClosed_iUnion_eq_univ
    hB_nonempty hB_disjoint hB_closed hB_cover

/--
The intersection graph of a finite nonempty relatively closed cover of a
preconnected set is connected.  Vertices are family indices and edges record
nonempty overlap inside the covered set.
-/
def setFamilyOverlapGraph {X ι : Type*} (s : Set X) (A : ι → Set X) :
    SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => ((A i ∩ s) ∩ (A j ∩ s)).Nonempty

/--
Finite closed-cover connectedness in graph form: every two members of a
nonempty finite relatively closed cover of a preconnected set are linked by a
chain of overlaps.
-/
theorem setFamilyOverlapGraph_connected_of_isPreconnected
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [Nonempty ι]
    {s : Set X} (hs : IsPreconnected s) (A : ι → Set X)
    (hnonempty : ∀ i, (A i ∩ s).Nonempty)
    (hclosed : ∀ i, IsClosed (A i ∩ s))
    (hcover : ⋃ i, A i ∩ s = s) :
    (setFamilyOverlapGraph s A).Connected := by
  classical
  let G : SimpleGraph ι := setFamilyOverlapGraph s A
  change G.Connected
  apply SimpleGraph.Connected.mk
  intro i j
  by_contra hnot
  let U : Set X := ⋃ k : {k : ι // G.Reachable i k}, A k ∩ s
  let V : Set X := ⋃ k : {k : ι // ¬ G.Reachable i k}, A k ∩ s
  have hU_closed : IsClosed U := by
    dsimp [U]
    exact isClosed_iUnion_of_finite fun k => hclosed k.1
  have hV_closed : IsClosed V := by
    dsimp [V]
    exact isClosed_iUnion_of_finite fun k => hclosed k.1
  have hU_nonempty : (s ∩ U).Nonempty := by
    rcases hnonempty i with ⟨x, hx⟩
    refine ⟨x, hx.2, ?_⟩
    simp only [U, Set.mem_iUnion]
    exact ⟨⟨i, SimpleGraph.Reachable.rfl⟩, hx⟩
  have hV_nonempty : (s ∩ V).Nonempty := by
    rcases hnonempty j with ⟨x, hx⟩
    refine ⟨x, hx.2, ?_⟩
    simp only [V, Set.mem_iUnion]
    exact ⟨⟨j, hnot⟩, hx⟩
  have hUV_cover : s ⊆ U ∪ V := by
    intro x hx
    have hxcover : x ∈ ⋃ k : ι, A k ∩ s := by
      rw [hcover]
      exact hx
    rcases Set.mem_iUnion.mp hxcover with ⟨k, hxk⟩
    by_cases hk : G.Reachable i k
    · left
      simp only [U, Set.mem_iUnion]
      exact ⟨⟨k, hk⟩, hxk⟩
    · right
      simp only [V, Set.mem_iUnion]
      exact ⟨⟨k, hk⟩, hxk⟩
  have hUV_disjoint : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    simp only [U, Set.mem_iUnion] at hxU
    simp only [V, Set.mem_iUnion] at hxV
    rcases hxU with ⟨k, hxk⟩
    rcases hxV with ⟨l, hxl⟩
    by_cases hkl : k.1 = l.1
    · apply l.2
      simpa only [hkl] using k.2
    · apply l.2
      apply k.2.trans
      apply SimpleGraph.Adj.reachable
      change k.1 ≠ l.1 ∧
        (((A k.1 ∩ s) ∩ (A l.1 ∩ s)).Nonempty ∨
          ((A l.1 ∩ s) ∩ (A k.1 ∩ s)).Nonempty)
      exact ⟨hkl, Or.inl ⟨x, hxk, hxl⟩⟩
  obtain ⟨x, hxS, hxU, hxV⟩ :=
    (isPreconnected_closed_iff.mp hs) U V hU_closed hV_closed hUV_cover hU_nonempty hV_nonempty
  exact Set.disjoint_left.mp hUV_disjoint hxU hxV

end AppliedModelingLib
