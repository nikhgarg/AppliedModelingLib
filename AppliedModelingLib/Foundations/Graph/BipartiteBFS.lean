import AppliedModelingLib.Foundations.Graph.GeodesicTree
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-!
# Breadth-first short cycles in bipartite graphs

This module formalizes the breadth-first-search part of the short-cycle
argument used after the two-one bipartite pruning step.  It constructs levels
and children from the canonical geodesic tree, rather than assuming a BFS
certificate.  If every nonisolated left vertex has degree at least three and
every nonisolated right vertex has degree at least two, the binary level count
forces a simple cycle of length at most `4 * log₂ |left|`.
-/

namespace AppliedModelingLib
namespace Foundations
namespace Graph

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bipartiteBoolColoring
    {G : SimpleGraph V} {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right) : G.Coloring Bool := by
  classical
  exact SimpleGraph.Coloring.mk (fun vertex => if vertex ∈ right then true else false) (by
    intro u v hadj
    rcases hBipartite.mem_of_adj hadj with hleft | hright
    · have huNot : u ∉ right := Set.disjoint_left.mp hBipartite.disjoint hleft.1
      simp [huNot, hleft.2]
    · have hvNot : v ∉ right := Set.disjoint_left.mp hBipartite.disjoint hright.2
      simp [hright.1, hvNot])

omit [Fintype V] [DecidableEq V] in
theorem bipartiteBoolColoring_eq_true_iff
    {G : SimpleGraph V} {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right) (vertex : V) :
    bipartiteBoolColoring hBipartite vertex = true ↔ vertex ∈ right := by
  classical
  change decide (vertex ∈ right) = true ↔ vertex ∈ right
  simp only [decide_eq_true_eq]

theorem geodesicTree_even_depth_mem_left
    {G : SimpleGraph V} {left right : Set V} (hBipartite : G.IsBipartiteWith left right)
    {root : V} (hroot : root ∈ left) (vertex : ReachableVertex G root)
    (heven : Even ((geodesicTree G root).dist (geodesicRoot G root) vertex)) :
    vertex.1 ∈ left := by
  let coloring := bipartiteBoolColoring hBipartite
  have hrootNot : ¬ coloring root = true := by
    have hrootNotRight : root ∉ right := Set.disjoint_left.mp hBipartite.disjoint hroot
    intro hrootColor
    exact hrootNotRight ((bipartiteBoolColoring_eq_true_iff hBipartite root).mp hrootColor)
  have hevenWalk : Even (shortestWalk G root vertex).length := by
    rw [shortestWalk_length, ← geodesicTree_dist_root G root vertex]
    exact heven
  have hcolor : coloring root = true ↔ coloring vertex.1 = true :=
    coloring.even_length_iff_congr (shortestWalk G root vertex) |>.mp hevenWalk
  have hvertexNot : ¬ coloring vertex.1 = true := by
    intro hvertex
    exact hrootNot (hcolor.mpr hvertex)
  by_cases hvertexRoot : vertex.1 = root
  · simpa [hvertexRoot] using hroot
  · rcases hBipartite.mem_of_adj (geodesicParent_adj G root vertex hvertexRoot) with hleft | hright
    · exfalso
      apply hvertexNot
      exact (bipartiteBoolColoring_eq_true_iff hBipartite vertex.1).mpr hleft.2
    · exact hright.2

theorem geodesicTree_odd_depth_mem_right
    {G : SimpleGraph V} {left right : Set V} (hBipartite : G.IsBipartiteWith left right)
    {root : V} (hroot : root ∈ left) (vertex : ReachableVertex G root)
    (hodd : Odd ((geodesicTree G root).dist (geodesicRoot G root) vertex)) :
    vertex.1 ∈ right := by
  let coloring := bipartiteBoolColoring hBipartite
  have hrootNot : ¬ coloring root = true := by
    have hrootNotRight : root ∉ right := Set.disjoint_left.mp hBipartite.disjoint hroot
    intro hrootColor
    exact hrootNotRight ((bipartiteBoolColoring_eq_true_iff hBipartite root).mp hrootColor)
  have hoddWalk : Odd (shortestWalk G root vertex).length := by
    rw [shortestWalk_length, ← geodesicTree_dist_root G root vertex]
    exact hodd
  have hcolor : (¬ coloring root = true) ↔ coloring vertex.1 = true :=
    coloring.odd_length_iff_not_congr (shortestWalk G root vertex) |>.mp hoddWalk
  have hvertex : coloring vertex.1 = true := hcolor.mp hrootNot
  exact (bipartiteBoolColoring_eq_true_iff hBipartite vertex.1).mp hvertex

noncomputable def geodesicLevel (G : SimpleGraph V) (root : V) (depth : Nat) :
    Finset (ReachableVertex G root) :=
  Finset.univ.filter fun vertex =>
    (geodesicTree G root).dist (geodesicRoot G root) vertex = depth

noncomputable def geodesicChildren (G : SimpleGraph V) (root : V)
    (parent : ReachableVertex G root) : Finset (ReachableVertex G root) :=
  Finset.univ.filter fun vertex =>
    vertex.1 ≠ root ∧ geodesicParent G root vertex = parent

theorem mem_geodesicLevel_iff (G : SimpleGraph V) (root : V) (depth : Nat)
    (vertex : ReachableVertex G root) :
    vertex ∈ geodesicLevel G root depth ↔
      (geodesicTree G root).dist (geodesicRoot G root) vertex = depth := by
  simp [geodesicLevel]

theorem mem_geodesicChildren_iff (G : SimpleGraph V) (root : V)
    (parent vertex : ReachableVertex G root) :
    vertex ∈ geodesicChildren G root parent ↔
      vertex.1 ≠ root ∧ geodesicParent G root vertex = parent := by
  simp [geodesicChildren]

theorem geodesicChildren_dist (G : SimpleGraph V) (root : V)
    {parent vertex : ReachableVertex G root}
    (hchild : vertex ∈ geodesicChildren G root parent) :
    (geodesicTree G root).dist (geodesicRoot G root) vertex =
      (geodesicTree G root).dist (geodesicRoot G root) parent + 1 := by
  rcases mem_geodesicChildren_iff G root parent vertex |>.mp hchild with ⟨hnotRoot, rfl⟩
  rw [geodesicTree_dist_root G root vertex,
    geodesicTree_dist_root G root (geodesicParent G root vertex)]
  exact (geodesicParent_dist G root vertex hnotRoot).symm

theorem geodesicLevel_succ_eq_biUnion (G : SimpleGraph V) (root : V) (depth : Nat) :
    geodesicLevel G root (depth + 1) =
      (geodesicLevel G root depth).biUnion (geodesicChildren G root) := by
  ext vertex
  simp only [Finset.mem_biUnion, mem_geodesicLevel_iff, mem_geodesicChildren_iff]
  constructor
  · intro hvertex
    have hnotRoot : vertex.1 ≠ root := by
      intro hroot
      have hvertexRoot : vertex = geodesicRoot G root := Subtype.ext hroot
      rw [hvertexRoot, SimpleGraph.dist_self] at hvertex
      omega
    refine ⟨geodesicParent G root vertex, ?_, hnotRoot, rfl⟩
    have hparent := geodesicParent_dist G root vertex hnotRoot
    rw [← geodesicTree_dist_root G root (geodesicParent G root vertex),
      ← geodesicTree_dist_root G root vertex] at hparent
    omega
  · rintro ⟨parent, hparent, hnotRoot, hparentEq⟩
    have hdist := geodesicParent_dist G root vertex hnotRoot
    rw [hparentEq, ← geodesicTree_dist_root G root parent,
      ← geodesicTree_dist_root G root vertex] at hdist
    omega

theorem geodesicChildren_pairwiseDisjoint (G : SimpleGraph V) (root : V) :
    Set.PairwiseDisjoint (Finset.univ : Finset (ReachableVertex G root))
      (geodesicChildren G root) := by
  intro parent hparent other hother hne
  apply Finset.disjoint_left.2
  intro vertex hvertexParent hvertexOther
  have hparentEq := (mem_geodesicChildren_iff G root parent vertex |>.mp hvertexParent).2
  have hotherEq := (mem_geodesicChildren_iff G root other vertex |>.mp hvertexOther).2
  exact hne (hparentEq.symm.trans hotherEq)

theorem geodesicLevel_card_succ (G : SimpleGraph V) (root : V) (depth : Nat) :
    (geodesicLevel G root (depth + 1)).card =
      ∑ parent ∈ geodesicLevel G root depth, (geodesicChildren G root parent).card := by
  rw [geodesicLevel_succ_eq_biUnion]
  apply Finset.card_biUnion
  exact (geodesicChildren_pairwiseDisjoint G root).subset (by simp)

theorem geodesicTree_degree_eq_of_no_short_cycle_of_depth_lt
    (G : SimpleGraph V) (root : V) (k : Nat)
    [DecidableRel G.Adj]
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length)
    {vertex : ReachableVertex G root}
    (hdepth : (geodesicTree G root).dist (geodesicRoot G root) vertex < 2 * k) :
    (geodesicTree G root).degree vertex = G.degree vertex.1 := by
  let toTree : G.neighborSet vertex.1 → (geodesicTree G root).neighborSet vertex :=
    fun neighbor => ⟨⟨neighbor.1, vertex.2.trans neighbor.2.reachable⟩,
      geodesicTree_adj_of_no_short_cycle_of_depth_lt G root k hnoCycle hdepth neighbor.2⟩
  let toGraph : (geodesicTree G root).neighborSet vertex → G.neighborSet vertex.1 :=
    fun neighbor => ⟨neighbor.1.1, geodesicTree_adj_sub G root neighbor.2⟩
  let equiv : G.neighborSet vertex.1 ≃ (geodesicTree G root).neighborSet vertex :=
    Equiv.ofBijective toTree (by
      constructor
      · intro first second heq
        apply Subtype.ext
        exact congrArg (fun neighbor => neighbor.1.1) heq
      · intro neighbor
        refine ⟨toGraph neighbor, ?_⟩
        apply Subtype.ext
        rfl)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using (Fintype.card_congr equiv).symm

theorem geodesicChildren_card_ge_degree_sub_one (G : SimpleGraph V) (root : V)
    (parent : ReachableVertex G root) :
    (geodesicTree G root).degree parent ≤
      (geodesicChildren G root parent).card + 1 := by
  have hsubset : (geodesicTree G root).neighborFinset parent ⊆
      insert (geodesicParent G root parent) (geodesicChildren G root parent) := by
    intro neighbor hneighbor
    rw [SimpleGraph.mem_neighborFinset] at hneighbor
    rcases (geodesicTree_adj_iff G root parent neighbor).mp hneighbor with hchild | hparent
    · exact Finset.mem_insert_of_mem
        ((mem_geodesicChildren_iff G root parent neighbor).mpr hchild)
    · rw [← hparent.2]
      simp
  calc
    (geodesicTree G root).degree parent =
        ((geodesicTree G root).neighborFinset parent).card := rfl
    _ ≤ (insert (geodesicParent G root parent) (geodesicChildren G root parent)).card :=
      Finset.card_le_card hsubset
    _ ≤ (geodesicChildren G root parent).card + 1 := Finset.card_insert_le _ _

theorem geodesicChildren_card_ge_degree_at_root (G : SimpleGraph V) (root : V) :
    (geodesicTree G root).degree (geodesicRoot G root) ≤
      (geodesicChildren G root (geodesicRoot G root)).card := by
  have hsubset : (geodesicTree G root).neighborFinset (geodesicRoot G root) ⊆
      geodesicChildren G root (geodesicRoot G root) := by
    intro neighbor hneighbor
    rw [SimpleGraph.mem_neighborFinset] at hneighbor
    rcases (geodesicTree_adj_iff G root (geodesicRoot G root) neighbor).mp hneighbor with
      hchild | hparent
    · exact (mem_geodesicChildren_iff G root (geodesicRoot G root) neighbor).mpr hchild
    · exact False.elim (hparent.1 rfl)
  calc
    (geodesicTree G root).degree (geodesicRoot G root) =
        ((geodesicTree G root).neighborFinset (geodesicRoot G root)).card := rfl
    _ ≤ (geodesicChildren G root (geodesicRoot G root)).card := Finset.card_le_card hsubset

theorem geodesicChildren_card_root_ge_three
    {G : SimpleGraph V} [DecidableRel G.Adj] {left : Set V}
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor)
    (k : Nat) (hk : 0 < k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    3 ≤ (geodesicChildren G root (geodesicRoot G root)).card := by
  have hdepth : (geodesicTree G root).dist (geodesicRoot G root)
      (geodesicRoot G root) < 2 * k := by
    rw [SimpleGraph.dist_self]
    omega
  have hdegree := geodesicTree_degree_eq_of_no_short_cycle_of_depth_lt G root k
    hnoCycle hdepth
  have hpositive : 0 < G.degree root :=
    (G.degree_pos_iff_exists_adj root).mpr ⟨neighbor, hrootAdj⟩
  have hlarge : 3 ≤ G.degree root := by
    rcases hleft root hroot with hzero | hlarge
    · omega
    · exact hlarge
  calc
    3 ≤ G.degree root := hlarge
    _ = (geodesicTree G root).degree (geodesicRoot G root) := hdegree.symm
    _ ≤ (geodesicChildren G root (geodesicRoot G root)).card :=
      geodesicChildren_card_ge_degree_at_root G root

theorem geodesicChildren_card_ge_two_of_left
    {G : SimpleGraph V} [DecidableRel G.Adj] {left : Set V}
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    {root : V} {parent : ReachableVertex G root}
    (hparentLeft : parent.1 ∈ left) (hparentPositive : 0 < G.degree parent.1)
    (k : Nat)
    (hdepth : (geodesicTree G root).dist (geodesicRoot G root) parent < 2 * k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    2 ≤ (geodesicChildren G root parent).card := by
  have hdegree := geodesicTree_degree_eq_of_no_short_cycle_of_depth_lt G root k
    hnoCycle hdepth
  have hlarge : 3 ≤ G.degree parent.1 := by
    rcases hleft parent.1 hparentLeft with hzero | hlarge
    · omega
    · exact hlarge
  have hchildren := geodesicChildren_card_ge_degree_sub_one G root parent
  omega

theorem geodesicChildren_card_ge_one_of_right
    {G : SimpleGraph V} [DecidableRel G.Adj] {right : Set V}
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root : V} {parent : ReachableVertex G root}
    (hparentRight : parent.1 ∈ right) (hparentPositive : 0 < G.degree parent.1)
    (k : Nat)
    (hdepth : (geodesicTree G root).dist (geodesicRoot G root) parent < 2 * k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    1 ≤ (geodesicChildren G root parent).card := by
  have hdegree := geodesicTree_degree_eq_of_no_short_cycle_of_depth_lt G root k
    hnoCycle hdepth
  have hlarge : 2 ≤ G.degree parent.1 := by
    rcases hright parent.1 hparentRight with hzero | hlarge
    · omega
    · exact hlarge
  have hchildren := geodesicChildren_card_ge_degree_sub_one G root parent
  omega

theorem geodesicLevel_zero_eq_singleton (G : SimpleGraph V) (root : V) :
    geodesicLevel G root 0 = {geodesicRoot G root} := by
  ext vertex
  rw [mem_geodesicLevel_iff]
  simp only [Finset.mem_singleton]
  exact ((geodesicTree_isTree G root).connected.dist_eq_zero_iff
    (u := geodesicRoot G root) (v := vertex)).trans eq_comm

theorem geodesicTree_positive_degree_of_positive_depth
    {G : SimpleGraph V} [DecidableRel G.Adj] {root : V}
    {vertex : ReachableVertex G root}
    (hpositiveDepth : 0 <
      (geodesicTree G root).dist (geodesicRoot G root) vertex) :
    0 < G.degree vertex.1 := by
  have hnotRoot : vertex.1 ≠ root := by
    intro hroot
    have hvertexRoot : vertex = geodesicRoot G root := Subtype.ext hroot
    rw [hvertexRoot, SimpleGraph.dist_self] at hpositiveDepth
    omega
  exact (G.degree_pos_iff_exists_adj vertex.1).mpr
    ⟨(geodesicParent G root vertex).1,
      (geodesicParent_adj G root vertex hnotRoot).symm⟩

theorem geodesicLevel_card_succ_ge_mul (G : SimpleGraph V) (root : V)
    (depth lower : Nat)
    (hchildren : ∀ parent : ReachableVertex G root, parent ∈ geodesicLevel G root depth →
      lower ≤ (geodesicChildren G root parent).card) :
    lower * (geodesicLevel G root depth).card ≤
      (geodesicLevel G root (depth + 1)).card := by
  rw [geodesicLevel_card_succ]
  calc
    lower * (geodesicLevel G root depth).card =
        ∑ parent ∈ geodesicLevel G root depth, lower := by simp [Nat.mul_comm]
    _ ≤ ∑ parent ∈ geodesicLevel G root depth,
        (geodesicChildren G root parent).card := by
      gcongr with parent hparent
      exact hchildren parent hparent

theorem geodesicLevel_one_card_ge_three
    {G : SimpleGraph V} [DecidableRel G.Adj] {left : Set V}
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor)
    (k : Nat) (hk : 0 < k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    3 ≤ (geodesicLevel G root 1).card := by
  have hrootChildren := geodesicChildren_card_root_ge_three hleft hroot hrootAdj k hk hnoCycle
  rw [show 1 = 0 + 1 by omega, geodesicLevel_card_succ,
    geodesicLevel_zero_eq_singleton]
  simpa using hrootChildren

theorem geodesicLevel_two_card_ge_three
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor)
    (k : Nat) (hk : 0 < k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    3 ≤ (geodesicLevel G root 2).card := by
  have hone := geodesicLevel_one_card_ge_three hleft hroot hrootAdj k hk hnoCycle
  have hnext := geodesicLevel_card_succ_ge_mul G root 1 1 (by
    intro parent hparent
    apply geodesicChildren_card_ge_one_of_right hright (k := k)
    · apply geodesicTree_odd_depth_mem_right hBipartite hroot parent
      rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      exact ⟨0, by omega⟩
    · apply geodesicTree_positive_degree_of_positive_depth
      rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      omega
    · rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      omega
    · exact hnoCycle)
  norm_num at hnext
  omega

theorem geodesicLevel_card_right_succ_ge_double
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    {root : V} (hroot : root ∈ left) (k i : Nat)
    (hi : 0 < i) (hik : i < k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    2 * (geodesicLevel G root (2 * i)).card ≤
      (geodesicLevel G root (2 * i + 1)).card := by
  have hnext := geodesicLevel_card_succ_ge_mul G root (2 * i) 2 (by
    intro parent hparent
    apply geodesicChildren_card_ge_two_of_left hleft (k := k)
    · apply geodesicTree_even_depth_mem_left hBipartite hroot parent
      rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      exact ⟨i, by omega⟩
    · apply geodesicTree_positive_degree_of_positive_depth
      rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      omega
    · rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      omega
    · exact hnoCycle)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnext

theorem geodesicLevel_card_left_succ_ge
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root : V} (hroot : root ∈ left) (k i : Nat)
    (hik : i < k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    (geodesicLevel G root (2 * i + 1)).card ≤
      (geodesicLevel G root (2 * i + 2)).card := by
  have hnext := geodesicLevel_card_succ_ge_mul G root (2 * i + 1) 1 (by
    intro parent hparent
    apply geodesicChildren_card_ge_one_of_right hright (k := k)
    · apply geodesicTree_odd_depth_mem_right hBipartite hroot parent
      rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      exact ⟨i, by omega⟩
    · apply geodesicTree_positive_degree_of_positive_depth
      rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      omega
    · rw [mem_geodesicLevel_iff] at hparent
      rw [hparent]
      omega
    · exact hnoCycle)
  norm_num at hnext
  exact hnext

theorem geodesicLevel_card_two_step_ge_double
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root : V} (hroot : root ∈ left) (k i : Nat)
    (hi : 0 < i) (hik : i < k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    2 * (geodesicLevel G root (2 * i)).card ≤
      (geodesicLevel G root (2 * (i + 1))).card := by
  have hrightStep := geodesicLevel_card_right_succ_ge_double
    hBipartite hleft hroot k i hi hik hnoCycle
  have hleftStep := geodesicLevel_card_left_succ_ge hBipartite hright hroot k i hik hnoCycle
  calc
    2 * (geodesicLevel G root (2 * i)).card ≤
        (geodesicLevel G root (2 * i + 2)).card := hrightStep.trans hleftStep
    _ = (geodesicLevel G root (2 * (i + 1))).card := by congr 2

theorem geodesicLevel_even_card_lower
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor)
    (k m : Nat) (hm : 0 < m) (hmk : m ≤ k)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    3 * 2 ^ (m - 1) ≤ (geodesicLevel G root (2 * m)).card := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hmzero : m = 0
    · subst m
      simpa using geodesicLevel_two_card_ge_three
        hBipartite hleft hright hroot hrootAdj k (by omega) hnoCycle
    · have hmpositive : 0 < m := Nat.pos_of_ne_zero hmzero
      have hmle : m ≤ k := by omega
      have hmlt : m < k := by omega
      have hprevious := ih hmpositive hmle
      have hstep := geodesicLevel_card_two_step_ge_double
        hBipartite hleft hright hroot k m hmpositive hmlt hnoCycle
      calc
        3 * 2 ^ (Nat.succ m - 1) = 3 * 2 ^ m := by rw [Nat.succ_sub_one]
        _ = 3 * 2 ^ ((m - 1) + 1) := by
          congr 2
          omega
        _ = 2 * (3 * 2 ^ (m - 1)) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * (geodesicLevel G root (2 * m)).card :=
          Nat.mul_le_mul_left _ hprevious
        _ ≤ (geodesicLevel G root (2 * Nat.succ m)).card := by
          simpa using hstep

noncomputable def geodesicEvenBall (G : SimpleGraph V) (root : V) (depth : Nat) :
    Finset (ReachableVertex G root) :=
  (Finset.range (depth + 1)).biUnion (fun index => geodesicLevel G root (2 * index))

theorem geodesicEvenBall_card (G : SimpleGraph V) (root : V) (depth : Nat) :
    (geodesicEvenBall G root depth).card =
      ∑ index ∈ Finset.range (depth + 1), (geodesicLevel G root (2 * index)).card := by
  unfold geodesicEvenBall
  apply Finset.card_biUnion
  intro first hfirst second hsecond hne
  apply Finset.disjoint_left.2
  intro vertex hfirstLevel hsecondLevel
  rw [mem_geodesicLevel_iff] at hfirstLevel hsecondLevel
  apply hne
  omega

theorem geodesicEvenBall_card_le_left_ncard
    {G : SimpleGraph V} {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    {root : V} (hroot : root ∈ left) (depth : Nat) :
    (geodesicEvenBall G root depth).card ≤ left.ncard := by
  classical
  have hsubset : (geodesicEvenBall G root depth).image Subtype.val ⊆ left.toFinset := by
    intro original horiginal
    rcases Finset.mem_image.mp horiginal with ⟨vertex, hvertex, rfl⟩
    rw [Set.mem_toFinset]
    apply geodesicTree_even_depth_mem_left hBipartite hroot vertex
    rcases Finset.mem_biUnion.mp hvertex with ⟨index, hindex, hlevel⟩
    rw [mem_geodesicLevel_iff] at hlevel
    rw [hlevel]
    exact ⟨index, by omega⟩
  calc
    (geodesicEvenBall G root depth).card =
        ((geodesicEvenBall G root depth).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ left.toFinset.card := Finset.card_le_card hsubset
    _ = left.ncard := (Set.ncard_eq_toFinset_card' left).symm

theorem rooted_binary_sum (depth : Nat) :
    (∑ index ∈ Finset.range (depth + 1),
      if index = 0 then 1 else 3 * 2 ^ (index - 1)) = 3 * 2 ^ depth - 2 := by
  induction depth with
  | zero => norm_num
  | succ depth ih =>
    rw [show Nat.succ depth + 1 = (depth + 1) + 1 by omega, Finset.sum_range_succ, ih]
    simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one, pow_succ]
    omega

theorem geodesicEvenBall_card_lower
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor)
    (k : Nat)
    (hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length) :
    3 * 2 ^ k - 2 ≤ (geodesicEvenBall G root k).card := by
  calc
    3 * 2 ^ k - 2 = ∑ index ∈ Finset.range (k + 1),
        if index = 0 then 1 else 3 * 2 ^ (index - 1) := (rooted_binary_sum k).symm
    _ ≤ ∑ index ∈ Finset.range (k + 1),
        (geodesicLevel G root (2 * index)).card := by
      gcongr with index hindex
      by_cases hzero : index = 0
      · subst index
        rw [geodesicLevel_zero_eq_singleton]
        simp
      · simp only [if_neg hzero]
        exact geodesicLevel_even_card_lower hBipartite hleft hright hroot hrootAdj
          k index (Nat.pos_of_ne_zero hzero) (by
            rw [Finset.mem_range] at hindex
            omega) hnoCycle
    _ = (geodesicEvenBall G root k).card := (geodesicEvenBall_card G root k).symm

theorem two_le_left_ncard_of_bipartite_two_one_stable
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor) :
    2 ≤ left.ncard := by
  classical
  have hneighborRight : neighbor ∈ right := by
    rcases hBipartite.mem_of_adj hrootAdj with hleft | hright
    · exact hleft.2
    · exact False.elim (Set.disjoint_left.mp hBipartite.disjoint hroot hright.1)
  have hpositive : 0 < G.degree neighbor :=
    (G.degree_pos_iff_exists_adj neighbor).mpr ⟨root, hrootAdj.symm⟩
  have hlarge : 2 ≤ G.degree neighbor := by
    rcases hright neighbor hneighborRight with hzero | hlarge
    · omega
    · exact hlarge
  obtain ⟨other, hotherAdj, hotherNe⟩ : ∃ other, G.Adj neighbor other ∧ other ≠ root := by
    by_contra hnot
    push Not at hnot
    have hsubset : G.neighborFinset neighbor ⊆ {root} := by
      intro other hother
      rw [SimpleGraph.mem_neighborFinset] at hother
      simp [hnot other hother]
    have hdegree : G.degree neighbor ≤ 1 := by
      calc
        G.degree neighbor = (G.neighborFinset neighbor).card := rfl
        _ ≤ ({root} : Finset V).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    omega
  have hotherLeft : other ∈ left := by
    rcases hBipartite.mem_of_adj hotherAdj with hleft | hright
    · exact False.elim (Set.disjoint_left.mp hBipartite.disjoint hleft.1 hneighborRight)
    · exact hright.2
  have hsubset : ({root, other} : Finset V) ⊆ left.toFinset := by
    intro vertex hvertex
    rw [Finset.mem_insert, Finset.mem_singleton] at hvertex
    rw [Set.mem_toFinset]
    rcases hvertex with rfl | rfl
    · exact hroot
    · exact hotherLeft
  calc
    2 = ({root, other} : Finset V).card := by simp [hotherNe.symm]
    _ ≤ left.toFinset.card := Finset.card_le_card hsubset
    _ = left.ncard := (Set.ncard_eq_toFinset_card' left).symm

theorem exists_simpleCycle_of_bipartite_two_one_stable_length_le_four_log
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle ∧
      cycle.length ≤ 4 * Nat.log 2 left.ncard := by
  classical
  by_contra hshort
  push Not at hshort
  let k := Nat.log 2 left.ncard
  have hnoCycle : ∀ {start : V} (cycle : G.Walk start start), cycle.IsCycle →
      4 * k < cycle.length := by
    intro start cycle hcycle
    exact hshort start cycle hcycle
  have hleftCard : 2 ≤ left.ncard :=
    two_le_left_ncard_of_bipartite_two_one_stable hBipartite hright hroot hrootAdj
  have hk : 0 < k := by
    apply Nat.lt_of_lt_of_le Nat.zero_lt_one
    apply Nat.le_log_of_pow_le
    · omega
    · norm_num
      exact hleftCard
  have hballLower := geodesicEvenBall_card_lower hBipartite hleft hright hroot hrootAdj
    k hnoCycle
  have hballUpper := geodesicEvenBall_card_le_left_ncard hBipartite hroot k
  have htwoPow : 2 ≤ 2 ^ k := by
    have hmono := Nat.pow_le_pow_right (by omega : 0 < 2) hk
    norm_num at hmono ⊢
    exact hmono
  have hpowBound : 2 ^ k.succ ≤ 3 * 2 ^ k - 2 := by
    rw [pow_succ]
    omega
  have hcontr : 2 ^ k.succ ≤ left.ncard :=
    hpowBound.trans (hballLower.trans hballUpper)
  have hlogBound : left.ncard < 2 ^ k.succ := by
    exact Nat.lt_pow_succ_log_self (by omega) left.ncard
  exact (Nat.not_lt_of_ge hcontr) hlogBound

/-- The natural-number cap constructed by the BFS proof is no larger than
the source's displayed real-log floor bound. -/
theorem four_natLog_le_two_natFloor_two_logb (n : Nat) :
    4 * Nat.log 2 n ≤ 2 * ⌊2 * Real.logb 2 n⌋₊ := by
  have hlog : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
  have hfloor : 2 * Nat.log 2 n ≤ ⌊2 * Real.logb 2 n⌋₊ := by
    apply Nat.le_floor
    norm_num
    exact hlog
  calc
    4 * Nat.log 2 n = 2 * (2 * Nat.log 2 n) := by ring
    _ ≤ 2 * ⌊2 * Real.logb 2 n⌋₊ := Nat.mul_le_mul_left _ hfloor

/-- Source-shaped version of the BFS short-cycle theorem, using the printed
base-two logarithm/floor notation. -/
theorem exists_simpleCycle_of_bipartite_two_one_stable_length_le_source_log_bound
    {G : SimpleGraph V} [DecidableRel G.Adj] {left right : Set V}
    (hBipartite : G.IsBipartiteWith left right)
    (hleft : ∀ vertex : V, vertex ∈ left →
      G.degree vertex = 0 ∨ 3 ≤ G.degree vertex)
    (hright : ∀ vertex : V, vertex ∈ right →
      G.degree vertex = 0 ∨ 2 ≤ G.degree vertex)
    {root neighbor : V} (hroot : root ∈ left) (hrootAdj : G.Adj root neighbor) :
    ∃ (start : V) (cycle : G.Walk start start), cycle.IsCycle ∧
      cycle.length ≤ 2 * ⌊2 * Real.logb 2 left.ncard⌋₊ := by
  obtain ⟨start, cycle, hcycle, hlength⟩ :=
    exists_simpleCycle_of_bipartite_two_one_stable_length_le_four_log
      hBipartite hleft hright hroot hrootAdj
  exact ⟨start, cycle, hcycle,
    hlength.trans (four_natLog_le_two_natFloor_two_logb left.ncard)⟩

end Graph
end Foundations
end AppliedModelingLib
