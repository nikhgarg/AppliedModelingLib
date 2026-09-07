import AppliedModelingLib.Foundations.Graph.SimpleCycleBounds

/-!
# Geodesic trees in finite simple graphs

This module constructs a genuine breadth-first spanning tree of a chosen
connected component.  It records the exact equality between tree depth and
ambient graph distance, then proves the first-non-tree-edge rule: if no short
cycle exists, every sufficiently shallow ambient edge is already a tree edge.
These are reusable finite graph foundations for short-cycle decompositions.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices reachable from a fixed root.  This is the natural finite carrier
for a breadth-first tree in one connected component. -/
abbrev ReachableVertex (G : SimpleGraph V) (root : V) :=
  { vertex : V // G.Reachable root vertex }

noncomputable instance instFintypeReachableVertex (G : SimpleGraph V) (root : V) :
    Fintype (ReachableVertex G root) :=
  Fintype.ofFinite _

noncomputable def shortestWalk (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) : G.Walk root vertex.1 :=
  (vertex.2.exists_path_of_dist).choose

theorem shortestWalk_isPath (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) :
    (shortestWalk G root vertex).IsPath :=
  (vertex.2.exists_path_of_dist).choose_spec.1

theorem shortestWalk_length (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) :
    (shortestWalk G root vertex).length = G.dist root vertex.1 :=
  (vertex.2.exists_path_of_dist).choose_spec.2

noncomputable def geodesicParent (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) : ReachableVertex G root :=
  if _ : vertex.1 = root then vertex else
    ⟨(shortestWalk G root vertex).penultimate,
      (shortestWalk G root vertex).dropLast.reachable⟩

theorem geodesicParent_eq_penultimate (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) (hroot : vertex.1 ≠ root) :
    (geodesicParent G root vertex).1 = (shortestWalk G root vertex).penultimate := by
  simp [geodesicParent, hroot]

theorem geodesicParent_adj (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) (hroot : vertex.1 ≠ root) :
    G.Adj (geodesicParent G root vertex).1 vertex.1 := by
  rw [geodesicParent_eq_penultimate G root vertex hroot]
  apply (shortestWalk G root vertex).adj_penultimate
  rw [SimpleGraph.Walk.not_nil_iff_lt_length, shortestWalk_length]
  exact vertex.2.pos_dist_of_ne hroot.symm

theorem geodesicParent_dist (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) (hroot : vertex.1 ≠ root) :
    G.dist root (geodesicParent G root vertex).1 + 1 = G.dist root vertex.1 := by
  have hshort := shortestWalk_length G root vertex
  have hdrop : G.dist root (geodesicParent G root vertex).1 ≤
      (shortestWalk G root vertex).dropLast.length := by
    rw [geodesicParent_eq_penultimate G root vertex hroot]
    exact SimpleGraph.dist_le (shortestWalk G root vertex).dropLast
  rw [SimpleGraph.Walk.length_dropLast, hshort] at hdrop
  have hpos : 0 < G.dist root vertex.1 :=
    vertex.2.pos_dist_of_ne hroot.symm
  have hadj := geodesicParent_adj G root vertex hroot
  rcases hadj.diff_dist_adj (u := root) with heq | hsucc | hpred
  · omega
  · omega
  · omega

noncomputable def geodesicTree (G : SimpleGraph V) (root : V) :
    SimpleGraph (ReachableVertex G root) where
  Adj u v :=
    (v.1 ≠ root ∧ geodesicParent G root v = u) ∨
      (u.1 ≠ root ∧ geodesicParent G root u = v)
  symm := by
    intro u v huv
    exact huv.symm
  loopless := ⟨by
    intro vertex hloop
    rcases hloop with hloop | hloop
    · have hdist := geodesicParent_dist G root vertex hloop.1
      rw [hloop.2] at hdist
      omega
    · have hdist := geodesicParent_dist G root vertex hloop.1
      rw [hloop.2] at hdist
      omega⟩

noncomputable instance instDecidableRelGeodesicTree (G : SimpleGraph V) (root : V) :
    DecidableRel (geodesicTree G root).Adj :=
  Classical.decRel _

theorem geodesicTree_adj_iff (G : SimpleGraph V) (root : V)
    (u v : ReachableVertex G root) :
    (geodesicTree G root).Adj u v ↔
      (v.1 ≠ root ∧ geodesicParent G root v = u) ∨
        (u.1 ≠ root ∧ geodesicParent G root u = v) := Iff.rfl

theorem geodesicTree_adj_sub (G : SimpleGraph V) (root : V)
    {u v : ReachableVertex G root} (hadj : (geodesicTree G root).Adj u v) :
    G.Adj u.1 v.1 := by
  rcases hadj with hadj | hadj
  · rw [← hadj.2]
    exact geodesicParent_adj G root v hadj.1
  · rw [← hadj.2]
    exact (geodesicParent_adj G root u hadj.1).symm

def geodesicRoot (G : SimpleGraph V) (root : V) : ReachableVertex G root :=
  ⟨root, (SimpleGraph.Walk.nil : G.Walk root root).reachable⟩

theorem geodesicTree_reachable_root (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) :
    (geodesicTree G root).Reachable (geodesicRoot G root) vertex := by
  induction hdist : G.dist root vertex.1 using Nat.strong_induction_on generalizing vertex with
  | h distance ih =>
    by_cases hroot : vertex.1 = root
    · have heq : vertex = geodesicRoot G root := by
        apply Subtype.ext
        exact hroot
      rw [heq]
    · let parent := geodesicParent G root vertex
      have hparent : G.dist root parent.1 < distance := by
        have hparentEq := geodesicParent_dist G root vertex hroot
        change G.dist root parent.1 + 1 = G.dist root vertex.1 at hparentEq
        rw [hdist] at hparentEq
        omega
      have hparentReach : (geodesicTree G root).Reachable (geodesicRoot G root) parent :=
        ih _ hparent parent rfl
      apply hparentReach.trans
      exact (geodesicTree_adj_iff G root parent vertex).2 (Or.inl ⟨hroot, rfl⟩) |>.reachable

theorem geodesicTree_connected (G : SimpleGraph V) (root : V) :
    (geodesicTree G root).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · intro u v
    exact (geodesicTree_reachable_root G root u).symm.trans
      (geodesicTree_reachable_root G root v)
  · exact ⟨geodesicRoot G root⟩

/-- The parent edge of each nonroot vertex, represented as an undirected
edge of the geodesic tree. -/
noncomputable def geodesicParentEdges (G : SimpleGraph V) (root : V) :
    Finset (Sym2 (ReachableVertex G root)) :=
  (Finset.univ.erase (geodesicRoot G root)).image
    (fun vertex => s(geodesicParent G root vertex, vertex))

theorem geodesicParentEdge_injOn (G : SimpleGraph V) (root : V) :
    Set.InjOn (fun vertex : ReachableVertex G root =>
      s(geodesicParent G root vertex, vertex))
      (↑(Finset.univ.erase (geodesicRoot G root)) : Set (ReachableVertex G root)) := by
  intro u hu v hv heq
  have huRoot : u.1 ≠ root := by
    intro hroot
    apply (Finset.mem_erase.mp hu).1
    apply Subtype.ext
    exact hroot
  have hvRoot : v.1 ≠ root := by
    intro hroot
    apply (Finset.mem_erase.mp hv).1
    apply Subtype.ext
    exact hroot
  rw [Sym2.eq_iff] at heq
  rcases heq with hsame | hswap
  · exact hsame.2
  · have huDist := geodesicParent_dist G root u huRoot
    have hvDist := geodesicParent_dist G root v hvRoot
    rw [hswap.1] at huDist
    rw [← hswap.2] at hvDist
    omega

theorem edgeFinset_geodesicTree (G : SimpleGraph V) (root : V) :
    (geodesicTree G root).edgeFinset = geodesicParentEdges G root := by
  classical
  ext edge
  refine Sym2.inductionOn edge (fun u v => ?_)
  rw [SimpleGraph.mem_edgeFinset]
  constructor
  · intro hadj
    rcases hadj with hadj | hadj
    · refine Finset.mem_image.mpr ⟨v, ?_, ?_⟩
      · rw [Finset.mem_erase]
        constructor
        · intro heq
          apply hadj.1
          exact congrArg Subtype.val heq
        · exact Finset.mem_univ _
      · simp [hadj.2]
    · refine Finset.mem_image.mpr ⟨u, ?_, ?_⟩
      · rw [Finset.mem_erase]
        constructor
        · intro heq
          apply hadj.1
          exact congrArg Subtype.val heq
        · exact Finset.mem_univ _
      · rw [hadj.2]
        exact Sym2.eq_swap
  · intro hmem
    rw [geodesicParentEdges, Finset.mem_image] at hmem
    rcases hmem with ⟨child, hchild, heq⟩
    rw [Finset.mem_erase] at hchild
    have hroot : child.1 ≠ root := by
      intro hroot
      apply hchild.1
      apply Subtype.ext
      exact hroot
    rw [← heq]
    exact Or.inl ⟨hroot, rfl⟩

theorem geodesicTree_card_edgeFinset (G : SimpleGraph V) (root : V) :
    (geodesicTree G root).edgeFinset.card + 1 = Fintype.card (ReachableVertex G root) := by
  classical
  have hpos : 0 < Fintype.card (ReachableVertex G root) :=
    Fintype.card_pos_iff.mpr ⟨geodesicRoot G root⟩
  rw [edgeFinset_geodesicTree, geodesicParentEdges,
    Finset.card_image_of_injOn (geodesicParentEdge_injOn G root),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  exact Nat.sub_add_cancel hpos

theorem geodesicTree_isTree (G : SimpleGraph V) (root : V) :
    (geodesicTree G root).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact geodesicTree_connected G root
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      Nat.card_eq_fintype_card]
    exact geodesicTree_card_edgeFinset G root

/-- Forgetting the reachability subtype maps the geodesic tree back into the
ambient graph without changing any tree edge. -/
def geodesicTreeHom (G : SimpleGraph V) (root : V) :
    geodesicTree G root →g G where
  toFun := Subtype.val
  map_rel' := geodesicTree_adj_sub G root

theorem original_dist_le_geodesicTree_dist (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) :
    G.dist root vertex.1 ≤
      (geodesicTree G root).dist (geodesicRoot G root) vertex := by
  obtain ⟨path, hpath, hlength⟩ :=
    (geodesicTree_isTree G root).connected (geodesicRoot G root) vertex |>.exists_path_of_dist
  have hmap : G.dist root vertex.1 ≤ (path.map (geodesicTreeHom G root)).length :=
    SimpleGraph.dist_le (path.map (geodesicTreeHom G root))
  simpa [SimpleGraph.Walk.length_map, hlength] using hmap

theorem geodesicTree_dist_root (G : SimpleGraph V) (root : V)
    (vertex : ReachableVertex G root) :
    (geodesicTree G root).dist (geodesicRoot G root) vertex = G.dist root vertex.1 := by
  induction hdist : G.dist root vertex.1 using Nat.strong_induction_on generalizing vertex with
  | h distance ih =>
    by_cases hroot : vertex.1 = root
    · have heq : vertex = geodesicRoot G root := by
        apply Subtype.ext
        exact hroot
      rw [heq, ← hdist, hroot]
      simp [geodesicRoot]
    · let parent := geodesicParent G root vertex
      have hparentDist : G.dist root parent.1 < distance := by
        have hparentEq := geodesicParent_dist G root vertex hroot
        change G.dist root parent.1 + 1 = G.dist root vertex.1 at hparentEq
        rw [hdist] at hparentEq
        omega
      have hparentTreeDist :
          (geodesicTree G root).dist (geodesicRoot G root) parent =
            G.dist root parent.1 :=
        ih _ hparentDist parent rfl
      have hparentEq := geodesicParent_dist G root vertex hroot
      change G.dist root parent.1 + 1 = G.dist root vertex.1 at hparentEq
      rcases (geodesicTree_isTree G root).dist_eq_dist_add_one_of_adj
          (geodesicRoot G root)
          ((geodesicTree_adj_iff G root parent vertex).2 (Or.inl ⟨hroot, rfl⟩)) with hback | hforward
      · have hlower := original_dist_le_geodesicTree_dist G root vertex
        exfalso
        omega
      · rw [hparentTreeDist, hparentEq] at hforward
        exact hforward.trans hdist

/-- The ambient graph restricted to the root's connected component, carried
on the reachability subtype used by the geodesic tree. -/
def reachableComponentGraph (G : SimpleGraph V) (root : V) :
    SimpleGraph (ReachableVertex G root) :=
  G.comap Subtype.val

def reachableComponentHom (G : SimpleGraph V) (root : V) :
    reachableComponentGraph G root →g G where
  toFun := Subtype.val
  map_rel' := by intro u v hadj; exact hadj

theorem geodesicTree_le_reachableComponentGraph (G : SimpleGraph V) (root : V) :
    geodesicTree G root ≤ reachableComponentGraph G root := by
  intro u v hadj
  exact geodesicTree_adj_sub G root hadj

/-- A non-tree edge of the actual geodesic tree yields a simple ambient
cycle.  Its length is exactly the tree distance between the edge endpoints
plus one, so a bound on the two root distances bounds the discovered cycle. -/
theorem exists_simpleCycle_of_geodesicTree_nonedge (G : SimpleGraph V) (root : V)
    {u v : ReachableVertex G root} (hnot : ¬ (geodesicTree G root).Adj u v)
    (hadj : G.Adj u.1 v.1) :
    ∃ cycle : G.Walk u.1 u.1, cycle.IsCycle ∧
      cycle.length = (geodesicTree G root).dist u v + 1 := by
  obtain ⟨cycle, hcycle, hlength⟩ :=
    exists_simpleCycle_of_tree_closing_edge
      (G := reachableComponentGraph G root) (T := geodesicTree G root)
      (geodesicTree_le_reachableComponentGraph G root)
      (geodesicTree_isTree G root) hnot hadj
  refine ⟨cycle.map (reachableComponentHom G root), ?_, ?_⟩
  · exact hcycle.map Subtype.val_injective
  · calc
      (cycle.map (reachableComponentHom G root)).length = cycle.length :=
        SimpleGraph.Walk.length_map _ _
      _ = (geodesicTree G root).dist u v + 1 := by
        simpa [SimpleGraph.dist_comm] using hlength

/-- If the ambient graph has no simple cycle of length at most `bound`, every
ambient edge whose two geodesic-tree depths sum to at most `bound - 1` is
already a tree edge.  This is the formal first-non-tree-edge stopping rule
for BFS. -/
theorem geodesicTree_adj_of_no_short_cycle (G : SimpleGraph V) (root : V)
    (bound : ℕ)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      bound < cycle.length)
    {u v : ReachableVertex G root} (hadj : G.Adj u.1 v.1)
    (hdepth : (geodesicTree G root).dist (geodesicRoot G root) u +
        (geodesicTree G root).dist (geodesicRoot G root) v + 1 ≤ bound) :
    (geodesicTree G root).Adj u v := by
  by_contra hnot
  obtain ⟨cycle, hcycle, hlength⟩ :=
    exists_simpleCycle_of_geodesicTree_nonedge G root hnot hadj
  have htriangle : (geodesicTree G root).dist u v ≤
      (geodesicTree G root).dist u (geodesicRoot G root) +
        (geodesicTree G root).dist (geodesicRoot G root) v := by
    exact (geodesicTree_isTree G root).connected.dist_triangle
  have htriangle' : (geodesicTree G root).dist u v ≤
      (geodesicTree G root).dist (geodesicRoot G root) u +
        (geodesicTree G root).dist (geodesicRoot G root) v := by
    calc
      (geodesicTree G root).dist u v ≤
          (geodesicTree G root).dist u (geodesicRoot G root) +
            (geodesicTree G root).dist (geodesicRoot G root) v := htriangle
      _ = (geodesicTree G root).dist (geodesicRoot G root) u +
            (geodesicTree G root).dist (geodesicRoot G root) v := by
          rw [SimpleGraph.dist_comm]
  have hshort : cycle.length ≤ bound := by
    rw [hlength]
    omega
  exact (Nat.not_lt_of_ge hshort) (hnoCycle cycle hcycle)

/-- In the `4k` short-cycle regime, every edge leaving a vertex of BFS depth
strictly below `2k` is itself a geodesic-tree edge. -/
theorem geodesicTree_adj_of_no_short_cycle_of_depth_lt (G : SimpleGraph V) (root : V)
    (k : ℕ)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length)
    {u : ReachableVertex G root}
    (hu : (geodesicTree G root).dist (geodesicRoot G root) u < 2 * k)
    {v : V} (hadj : G.Adj u.1 v) :
    (geodesicTree G root).Adj u
      (⟨v, u.2.trans hadj.reachable⟩ : ReachableVertex G root) := by
  let w : ReachableVertex G root := ⟨v, u.2.trans hadj.reachable⟩
  have hdist_v : G.dist root w.1 ≤ G.dist root u.1 + 1 := by
    calc
      G.dist root w.1 ≤ ((shortestWalk G root u).concat hadj).length := by
        change G.dist root v ≤ ((shortestWalk G root u).concat hadj).length
        exact SimpleGraph.dist_le ((shortestWalk G root u).concat hadj)
      _ = G.dist root u.1 + 1 := by
        rw [SimpleGraph.Walk.length_concat, shortestWalk_length]
  have hu' : G.dist root u.1 < 2 * k := by
    rw [← geodesicTree_dist_root G root u]
    exact hu
  have hdepth : (geodesicTree G root).dist (geodesicRoot G root) u +
      (geodesicTree G root).dist (geodesicRoot G root) w + 1 ≤ 4 * k := by
    rw [geodesicTree_dist_root G root u, geodesicTree_dist_root G root w]
    omega
  exact geodesicTree_adj_of_no_short_cycle G root (4 * k) hnoCycle hadj hdepth

end Graph
end Foundations
end AppliedModelingLib
