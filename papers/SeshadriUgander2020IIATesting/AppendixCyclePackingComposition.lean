import SeshadriUgander2020IIATesting.CyclePackingAlternatingWitness
import SeshadriUgander2020IIATesting.AppendixCycleStatistics

/-!
# Composition of the two Appendix-Lemma-10 cycle phases

The short-cycle trace of Appendix Lemma 9 selects an edge-disjoint family but
leaves a small residual.  This module proves that, under the paper's Eulerian
assumption, that *actual residual* is still Eulerian and bipartite.  It can
therefore be decomposed into `2n`-bounded simple cycles and appended to the
short phase without changing either phase's edge support.
-/

namespace SeshadriUgander2020IIATesting

namespace ChoiceFrame

open AppliedModelingLib.Foundations.Graph

variable (F : ChoiceFrame)

/-- Removing the edges selected by a partial incidence-cycle packing preserves
the same item/set bipartition. -/
theorem partialPacking_residual_isBipartiteWith
    {maxLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength) :
    P.residual.IsBipartiteWith F.itemVertices F.setVertices := by
  have hresidualLe : P.residual ≤ F.incidenceGraph := by
    exact sdiff_le
  constructor
  · exact F.incidenceGraph_isBipartiteWith.disjoint
  · intro u v hadj
    exact F.incidenceGraph_isBipartiteWith.mem_of_adj (hresidualLe hadj)

/-- The selected simple cycles form an even-degree graph, so deleting them
from an Eulerian incidence graph leaves an Eulerian residual. -/
theorem eulerian_partialPacking_residual_even_degree
    {maxLength : Nat}
    (hEulerian : F.Eulerian)
    (P : PartialSimpleCyclePacking F.incidenceGraph maxLength) :
    ∀ vertex : Sum F.Item F.SetId, Even (P.residual.degree vertex) := by
  have hresidual := P.even_degree_sdiff_usedEdges_of_even_degree
    ((F.eulerian_iff_incidenceGraph_even_degree).mp hEulerian)
    P.even_degree_usedEdgesGraph
  have hcount : ∀ vertex : Sum F.Item F.SetId,
      Even (degreeCount (F.incidenceGraph \ SimpleGraph.fromEdgeSet
        (↑P.usedEdges : Set (Sym2 (Sum F.Item F.SetId)))) vertex) := by
    intro vertex
    rw [degreeCount_eq_degree]
    exact hresidual vertex
  intro vertex
  rw [← degreeCount_eq_degree]
  change Even (degreeCount (F.incidenceGraph \ SimpleGraph.fromEdgeSet
    (↑P.usedEdges : Set (Sym2 (Sum F.Item F.SetId)))) vertex)
  exact hcount vertex

/-- The short Appendix-Lemma-9 packing and the complete long-cycle packing of
its concrete residual.  The first packing has the source logarithmic cap; the
second covers exactly the unselected edges and has the source `2n` cap. -/
theorem eulerian_incidenceGraph_has_short_residual_cycle_packings
    (hEulerian : F.Eulerian) :
    ∃ (P : PartialSimpleCyclePacking F.incidenceGraph
          (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
      (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item)),
      F.incidenceCount - P.usedEdges.card ≤
        min (2 * Fintype.card F.Item + Fintype.card F.SetId)
          (4 * Fintype.card F.Item) ∧
      Q.IsComplete := by
  obtain ⟨P, hbudget⟩ :=
    F.eulerian_incidenceGraph_has_source_short_cycle_packing hEulerian
  have hpeeling : HasBoundedSimpleCyclePeeling (2 * Fintype.card F.Item)
      P.residual := by
    have h := exists_boundedSimpleCyclePeeling_of_even_degree_of_isBipartiteWith
      (F.partialPacking_residual_isBipartiteWith P)
      (F.eulerian_partialPacking_residual_even_degree hEulerian P)
    rw [F.itemVertices_ncard] at h
    exact h
  obtain ⟨Q, hcomplete⟩ :=
    PartialSimpleCyclePacking.exists_complete_of_boundedSimpleCyclePeeling hpeeling
  exact ⟨P, Q, hbudget, hcomplete⟩

/-- The long residual phase, lifted back to the original incidence graph, is
edge-disjoint from the selected short phase. -/
theorem shortPacking_disjoint_lift_residual_packing
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength) :
    Disjoint P.usedEdges (Q.lift sdiff_le).usedEdges := by
  rw [Q.usedEdges_lift sdiff_le]
  apply Finset.disjoint_left.mpr
  intro edge hshort hlong
  have hresidual := Q.usedEdges_subset_edgeFinset hlong
  rw [SimpleGraph.mem_edgeFinset, P.edgeSet_residual] at hresidual
  exact hresidual.2 hshort

/-- The union of the short phase and a complete residual packing covers every
original incidence edge. -/
theorem shortPacking_lift_residual_usedEdges_cover
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    (↑P.usedEdges : Set (Sym2 (Sum F.Item F.SetId))) ∪
        (↑(Q.lift sdiff_le).usedEdges : Set (Sym2 (Sum F.Item F.SetId))) =
      F.incidenceGraph.edgeSet := by
  change (↑Q.usedEdges : Set (Sym2 (Sum F.Item F.SetId))) = P.residual.edgeSet at hQcomplete
  rw [Q.usedEdges_lift sdiff_le]
  ext edge
  simp only [Set.mem_union]
  constructor
  · rintro (hshort | hresidual)
    · have hfinite := P.usedEdges_subset_edgeFinset hshort
      rwa [SimpleGraph.mem_edgeFinset] at hfinite
    · have hresidualEdge : edge ∈ P.residual.edgeSet := by
        change edge ∈ (↑Q.usedEdges : Set (Sym2 (Sum F.Item F.SetId))) at hresidual
        exact hQcomplete ▸ hresidual
      rw [P.edgeSet_residual] at hresidualEdge
      exact hresidualEdge.1
  · intro hedge
    by_cases hshort : edge ∈ P.usedEdges
    · exact Or.inl hshort
    · apply Or.inr
      have hresidualEdge : edge ∈ P.residual.edgeSet := by
        rw [P.edgeSet_residual]
        exact ⟨hedge, hshort⟩
      change edge ∈ (↑Q.usedEdges : Set (Sym2 (Sum F.Item F.SetId)))
      exact hQcomplete.symm ▸ hresidualEdge

/-- The total length of a complete packing of the short phase's residual is
exactly the number of incidences left unselected by that short phase. -/
theorem sum_length_residual_complete_packing_eq_unselected
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    (∑ cycle : Q.Cycle, (Q.walk cycle).2.length) =
      F.incidenceCount - P.usedEdges.card := by
  calc
    (∑ cycle : Q.Cycle, (Q.walk cycle).2.length) =
        Fintype.card P.residual.edgeSet :=
      Q.sum_length_eq_edgeSet_card hQcomplete
    _ = P.residual.edgeFinset.card := SimpleGraph.edgeFinset_card.symm
    _ = F.incidenceGraph.edgeFinset.card - P.usedEdges.card :=
      P.card_edgeFinset_residual
    _ = F.incidenceCount - P.usedEdges.card := by
      rw [F.incidenceGraph_edgeFinset_card]

/-- The complete packing obtained by placing the residual cycles after the
short cycles. Its sum-tagged cycle index retains the two source phases. -/
noncomputable def composedPacking
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength) :
    PartialSimpleCyclePacking F.incidenceGraph (max shortLength longLength) :=
  P.append (Q.lift sdiff_le)
    (F.shortPacking_disjoint_lift_residual_packing P Q)

/-- The composed packing is complete when the residual phase is complete. -/
theorem composedPacking_isComplete
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    (F.composedPacking P Q).IsComplete := by
  exact P.isComplete_append_of_usedEdges_union (Q.lift sdiff_le)
    (F.shortPacking_disjoint_lift_residual_packing P Q)
    (F.shortPacking_lift_residual_usedEdges_cover P Q hQcomplete)

/-- The signed decomposition associated to the composed graph packing. -/
noncomputable def composedCycleDecomposition
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) : ChoiceSystem.CycleDecomposition F :=
  F.cycleDecompositionOfCompletePacking (F.composedPacking P Q)
    (F.composedPacking_isComplete P Q hQcomplete)

/-- The signed decomposition obtained by concatenating the two Appendix
packing phases has the concrete alternating traversal required by Lemma 2. -/
noncomputable def composedCycleDecomposition_alternatingCycleWitness
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    (F.composedCycleDecomposition P Q hQcomplete).AlternatingCycleWitness :=
  F.cycleDecompositionOfCompletePacking_alternatingCycleWitness
    (F.composedPacking P Q) (F.composedPacking_isComplete P Q hQcomplete)

/-- The residual cycles are the exceptional (long-cycle) tier in the composed
signed decomposition. -/
noncomputable def composedExceptional
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    Finset (F.composedPacking P Q).Cycle :=
  by
    classical
    let embedding : Q.Cycle ↪ (F.composedPacking P Q).Cycle :=
      ⟨Sum.inr, Sum.inr_injective⟩
    exact Finset.univ.map embedding

theorem composedCycleDecomposition_cycle_eq_sum
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    (F.composedCycleDecomposition P Q hQcomplete).Cycle = Sum P.Cycle Q.Cycle := rfl

@[simp] theorem mem_composedExceptional_inl
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) (cycle : P.Cycle) :
    Sum.inl cycle ∉ F.composedExceptional P Q hQcomplete := by
  intro hmem
  unfold composedExceptional at hmem
  dsimp only at hmem
  rcases Finset.mem_map.mp hmem with ⟨other, _, heq⟩
  change Sum.inr other = Sum.inl cycle at heq
  exact Sum.inr_ne_inl heq

@[simp] theorem mem_composedExceptional_inr
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) (cycle : Q.Cycle) :
    Sum.inr cycle ∈ F.composedExceptional P Q hQcomplete := by
  unfold composedExceptional
  dsimp only
  apply Finset.mem_map.mpr
  exact ⟨cycle, Finset.mem_univ _, rfl⟩

/-- A left-tagged composed cycle has exactly its original short-phase length. -/
theorem composedCycleDecomposition_length_inl
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) (cycle : P.Cycle) :
    (F.composedCycleDecomposition P Q hQcomplete).length (Sum.inl cycle) =
      (P.walk cycle).2.length := by
  unfold composedCycleDecomposition
  rw [F.cycleDecompositionOfCompletePacking_length]
  rfl

/-- A right-tagged composed cycle has exactly its residual-phase length. -/
theorem composedCycleDecomposition_length_inr
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) (cycle : Q.Cycle) :
    (F.composedCycleDecomposition P Q hQcomplete).length (Sum.inr cycle) =
      (Q.walk cycle).2.length := by
  unfold composedCycleDecomposition
  rw [F.cycleDecompositionOfCompletePacking_length]
  change ((Q.lift sdiff_le).walk cycle).2.length = (Q.walk cycle).2.length
  exact Q.length_lift sdiff_le cycle

/-- The exceptional tier has exactly the residual's edge mass, hence exactly
the number of short-phase incidences left unselected. -/
theorem sum_composedExceptional_length_eq_unselected
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    (∑ cycle ∈ F.composedExceptional P Q hQcomplete,
      ((F.composedCycleDecomposition P Q hQcomplete).length cycle : ℝ)) =
      (F.incidenceCount - P.usedEdges.card : ℝ) := by
  classical
  let E : Q.Cycle ≃
      {cycle : (F.composedPacking P Q).Cycle //
        cycle ∈ F.composedExceptional P Q hQcomplete} :=
    Equiv.ofBijective
      (fun cycle => ⟨Sum.inr cycle,
        F.mem_composedExceptional_inr P Q hQcomplete cycle⟩)
      (by
        constructor
        · intro first second heq
          apply Sum.inr.inj
          exact congrArg Subtype.val heq
        · rintro ⟨cycle, hcycle⟩
          unfold composedExceptional at hcycle
          dsimp only at hcycle
          rcases Finset.mem_map.mp hcycle with ⟨preimage, _, hpreimage⟩
          refine ⟨preimage, ?_⟩
          apply Subtype.ext
          exact hpreimage)
  have hsum :
      (∑ cycle : Q.Cycle, ((Q.walk cycle).2.length : ℝ)) =
        ∑ cycle : {cycle : (F.composedPacking P Q).Cycle //
          cycle ∈ F.composedExceptional P Q hQcomplete},
          ((F.composedCycleDecomposition P Q hQcomplete).length cycle.1 : ℝ) := by
    apply Fintype.sum_equiv E
    intro cycle
    simpa [E] using congrArg (fun length : ℕ => (length : ℝ))
      (F.composedCycleDecomposition_length_inr P Q hQcomplete cycle).symm
  have htotal :
      (∑ cycle : Q.Cycle, ((Q.walk cycle).2.length : ℝ)) =
        (F.incidenceCount - P.usedEdges.card : ℝ) := by
    have hcardle : P.usedEdges.card ≤ F.incidenceCount := by
      rw [← F.incidenceGraph_edgeFinset_card]
      exact Finset.card_le_card P.usedEdges_subset_edgeFinset
    rw [← Nat.cast_sub hcardle]
    exact_mod_cast F.sum_length_residual_complete_packing_eq_unselected P Q hQcomplete
  change (∑ cycle ∈ F.composedExceptional P Q hQcomplete,
    ((F.composedCycleDecomposition P Q hQcomplete).length cycle : ℝ)) =
    (F.incidenceCount - P.usedEdges.card : ℝ)
  have hsubtype :
      (∑ cycle ∈ F.composedExceptional P Q hQcomplete,
        ((F.composedCycleDecomposition P Q hQcomplete).length cycle : ℝ)) =
        ∑ cycle : {cycle : (F.composedPacking P Q).Cycle //
          cycle ∈ F.composedExceptional P Q hQcomplete},
          ((F.composedCycleDecomposition P Q hQcomplete).length cycle.1 : ℝ) := by
    exact (F.composedExceptional P Q hQcomplete).sum_subtype
      (fun cycle => Iff.rfl)
      (fun cycle => ((F.composedCycleDecomposition P Q hQcomplete).length cycle : ℝ))
  rw [hsubtype, ← hsum]
  exact htotal

/-- The elementary integer inequality behind the source observation that the
logarithmic short-cycle cap never exceeds the two-times-n residual-cycle cap. -/
private theorem nat_sq_lt_two_pow_succ (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 < 2 ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rcases hn.eq_or_lt with rfl | hnthree
    · norm_num
    · have hpoly : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := hpoly
        _ < 2 * 2 ^ (n + 1) := Nat.mul_lt_mul_of_pos_left ih (by omega)
        _ = 2 ^ ((n + 1) + 1) := by ring

/-- The elementary exponential comparison used when weakening the exact
short-cycle cap to the source's real-logarithmic display. -/
private theorem nat_sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) :
    n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpoly : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc
      (n + 1) ^ 2 ≤ 2 * n ^ 2 := hpoly
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by ring

/-- For at least four items, the source's real-logarithmic weakening remains
below the extremal `2n` cap.  The exceptional three-item case is therefore
kept out of the simplified display and handled by the unconditional cap. -/
private theorem four_mul_logb_le_two_mul (n : ℕ) (hn : 4 ≤ n) :
    4 * Real.logb 2 n ≤ 2 * n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hsqNat := nat_sq_le_two_pow n hn
  have hsqReal : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hsqNat
  have hrpowPos : 0 ≤ (2 : ℝ) ^ ((n : ℝ) / 2) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hrpowSq : ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ n := by
    calc
      ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 =
          ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (2 : ℝ) ^ (((n : ℝ) / 2) * 2) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = (2 : ℝ) ^ (n : ℝ) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ n := Real.rpow_natCast _ _
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
    apply (sq_le_sq₀ (Nat.cast_nonneg n) hrpowPos).mp
    rw [hrpowSq]
    exact hsqReal
  have hlog : Real.logb 2 (n : ℝ) ≤ (n : ℝ) / 2 :=
    (Real.logb_le_iff_le_rpow (by norm_num) hnpos).mpr hpow
  nlinarith

/-- The source logarithmic cap is positive for every nontrivial item
universe, so the mean-bound divisions have their intended sign. -/
private theorem source_shortCycle_cap_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < 2 * (⌊2 * Real.logb 2 n⌋₊ : ℝ) := by
  have hlog : (1 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num)
      (by exact_mod_cast hn)
  have hfloor : 2 ≤ ⌊2 * Real.logb 2 (n : ℝ)⌋₊ := by
    apply Nat.le_floor
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * Real.logb 2 (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hfloorPos : 0 < (⌊2 * Real.logb 2 (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (show 0 < ⌊2 * Real.logb 2 (n : ℝ)⌋₊ by omega)
  positivity

/-- For every nontrivial item universe, the source short-cycle cap is no
larger than the two-times-n cap used for the Eulerian residual phase. -/
theorem source_shortCycle_cap_le_two_mul (n : ℕ) (hn : 2 ≤ n) :
    2 * ⌊2 * Real.logb 2 n⌋₊ ≤ 2 * n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hsqNat := nat_sq_lt_two_pow_succ n hn
  have hsqReal : (n : ℝ) ^ 2 < (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast hsqNat
  have hrpowPos : 0 < (2 : ℝ) ^ (((n : ℝ) + 1) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrpowSq :
      ((2 : ℝ) ^ (((n : ℝ) + 1) / 2)) ^ 2 = (2 : ℝ) ^ (n + 1) := by
    calc
      ((2 : ℝ) ^ (((n : ℝ) + 1) / 2)) ^ 2 =
          ((2 : ℝ) ^ (((n : ℝ) + 1) / 2)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (2 : ℝ) ^ ((((n : ℝ) + 1) / 2) * 2) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ = (2 : ℝ) ^ ((n + 1 : ℕ) : ℝ) := by
        congr 1
        norm_num
      _ = (2 : ℝ) ^ (n + 1) := Real.rpow_natCast _ _
  have hpow : (n : ℝ) < (2 : ℝ) ^ (((n : ℝ) + 1) / 2) := by
    apply (sq_lt_sq₀ (Nat.cast_nonneg n) hrpowPos.le).mp
    rw [hrpowSq]
    exact hsqReal
  have hlog : Real.logb 2 (n : ℝ) < ((n : ℝ) + 1) / 2 :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) hnpos).mpr hpow
  have hlogFloor : ⌊2 * Real.logb 2 n⌋₊ ≤ n := by
    apply Nat.le_of_lt_succ
    rw [Nat.floor_lt]
    · norm_num [Nat.cast_succ]
      nlinarith
    · exact mul_nonneg (by positivity)
        (Real.logb_nonneg (by norm_num)
          (by exact_mod_cast (show 1 ≤ n by omega)))
  exact Nat.mul_le_mul_left 2 hlogFloor

/-- The choice-frame assumptions imply that its item universe has at least
two elements. -/
theorem itemCard_two_le : 2 ≤ Fintype.card F.Item := by
  obtain ⟨setId⟩ := F.nonempty_sets
  exact (F.card_two_le setId).trans (Finset.card_le_univ (F.members setId))

/-- Concrete two-tier statistics for a composed packing.  The short cap is
the first phase's cap; the long cap is the larger of the two phase caps,
which is sufficient before the source's elementary comparison of the two
displayed caps is applied. -/
noncomputable def composedTwoTierCycleBounds
    {shortLength longLength : Nat}
    (P : PartialSimpleCyclePacking F.incidenceGraph shortLength)
    (Q : PartialSimpleCyclePacking P.residual longLength)
    (hQcomplete : Q.IsComplete) :
    (F.composedCycleDecomposition P Q hQcomplete).TwoTierCycleBounds where
  exceptional := F.composedExceptional P Q hQcomplete
  shortBound := shortLength
  longBound := max (shortLength : ℝ) longLength
  exceptionalMassBound := F.incidenceCount - P.usedEdges.card
  shortBound_nonneg := Nat.cast_nonneg _
  short_le_long := le_max_left _ _
  short_length_le := by
    intro cycle hnot
    cases cycle with
    | inl shortCycle =>
      rw [F.composedCycleDecomposition_length_inl]
      exact_mod_cast P.length_le shortCycle
    | inr longCycle =>
      exact False.elim (hnot (F.mem_composedExceptional_inr P Q hQcomplete longCycle))
  exceptional_length_le := by
    intro cycle hmem
    cases cycle with
    | inl shortCycle =>
      exact False.elim ((F.mem_composedExceptional_inl P Q hQcomplete shortCycle) hmem)
    | inr longCycle =>
      rw [F.composedCycleDecomposition_length_inr]
      calc
        ((Q.walk longCycle).2.length : ℝ) ≤ longLength := by
          exact_mod_cast Q.length_le longCycle
        _ ≤ max (shortLength : ℝ) longLength := le_max_right _ _
  exceptional_mass_le := le_of_eq
    (F.sum_composedExceptional_length_eq_unselected P Q hQcomplete)

/-- The source-capped two-tier data for Appendix Lemma 10. Its exceptional
mass is bounded by the precise pruning budget, while its individual caps are
the source logarithmic cap and the two-times-n residual cap. -/
noncomputable def sourceComposedTwoTierCycleBounds
    (P : PartialSimpleCyclePacking F.incidenceGraph
      (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
    (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
    (hQcomplete : Q.IsComplete)
    (budget : ℕ)
    (hbudget : F.incidenceCount - P.usedEdges.card ≤ budget) :
    (F.composedCycleDecomposition P Q hQcomplete).TwoTierCycleBounds where
  exceptional := F.composedExceptional P Q hQcomplete
  shortBound := 2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊
  longBound := 2 * Fintype.card F.Item
  exceptionalMassBound := budget
  shortBound_nonneg := by positivity
  short_le_long := by
    exact_mod_cast source_shortCycle_cap_le_two_mul
      (Fintype.card F.Item) F.itemCard_two_le
  short_length_le := by
    intro cycle hnot
    cases cycle with
    | inl shortCycle =>
      rw [F.composedCycleDecomposition_length_inl]
      exact_mod_cast P.length_le shortCycle
    | inr longCycle =>
      exact False.elim (hnot (F.mem_composedExceptional_inr P Q hQcomplete longCycle))
  exceptional_length_le := by
    intro cycle hmem
    cases cycle with
    | inl shortCycle =>
      exact False.elim ((F.mem_composedExceptional_inl P Q hQcomplete shortCycle) hmem)
    | inr longCycle =>
      rw [F.composedCycleDecomposition_length_inr]
      exact_mod_cast Q.length_le longCycle
  exceptional_mass_le := by
    have hcardle : P.usedEdges.card ≤ F.incidenceCount := by
      rw [← F.incidenceGraph_edgeFinset_card]
      exact Finset.card_le_card P.usedEdges_subset_edgeFinset
    calc
      (∑ cycle ∈ F.composedExceptional P Q hQcomplete,
          ((F.composedCycleDecomposition P Q hQcomplete).length cycle : ℝ)) =
          (F.incidenceCount - P.usedEdges.card : ℝ) :=
        F.sum_composedExceptional_length_eq_unselected P Q hQcomplete
      _ = ((F.incidenceCount - P.usedEdges.card : ℕ) : ℝ) :=
        (Nat.cast_sub hcardle).symm
      _ ≤ budget := by exact_mod_cast hbudget

/-- Appendix Lemma 10's two graph phases concatenate to one complete packing.
The sum-tagged cycle type preserves which cycles received the short logarithmic
bound and which came from the `2n` residual phase. -/
theorem eulerian_incidenceGraph_exists_composed_cycle_packing
    (hEulerian : F.Eulerian) :
    ∃ (P : PartialSimpleCyclePacking F.incidenceGraph
          (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
      (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item)),
      F.incidenceCount - P.usedEdges.card ≤
        min (2 * Fintype.card F.Item + Fintype.card F.SetId)
          (4 * Fintype.card F.Item) ∧
      (P.append (Q.lift sdiff_le)
        (F.shortPacking_disjoint_lift_residual_packing P Q)).IsComplete := by
  obtain ⟨P, Q, hbudget, hQcomplete⟩ :=
    F.eulerian_incidenceGraph_has_short_residual_cycle_packings hEulerian
  refine ⟨P, Q, hbudget, ?_⟩
  exact P.isComplete_append_of_usedEdges_union (Q.lift sdiff_le)
    (F.shortPacking_disjoint_lift_residual_packing P Q)
    (F.shortPacking_lift_residual_usedEdges_cover P Q hQcomplete)

/-- Source-faithful two-phase cycle data for Appendix Lemma 10: pruning gives
the logarithmic phase and its residual budget, and Eulerian decomposition gives
the `2n` residual phase. -/
theorem eulerian_incidenceGraph_exists_source_twoTierCycleBounds
    (hEulerian : F.Eulerian) :
    ∃ (P : PartialSimpleCyclePacking F.incidenceGraph
          (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
      (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
      (hQcomplete : Q.IsComplete),
      F.incidenceCount - P.usedEdges.card ≤
        min (2 * Fintype.card F.Item + Fintype.card F.SetId)
          (4 * Fintype.card F.Item) ∧
      let D := F.composedCycleDecomposition P Q hQcomplete
      ∃ B : D.TwoTierCycleBounds,
        B.shortBound = 2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊ ∧
        B.longBound = 2 * Fintype.card F.Item ∧
        B.exceptionalMassBound =
          min (2 * Fintype.card F.Item + Fintype.card F.SetId)
            (4 * Fintype.card F.Item) := by
  obtain ⟨P, Q, hbudget, hQcomplete⟩ :=
    F.eulerian_incidenceGraph_has_short_residual_cycle_packings hEulerian
  refine ⟨P, Q, hQcomplete, hbudget, ?_⟩
  dsimp
  refine ⟨F.sourceComposedTwoTierCycleBounds P Q hQcomplete _ hbudget, rfl, rfl, rfl⟩

/-- The constructed two-phase decomposition has the exact Appendix-Lemma-10
dispersion bound before the source weakens its logarithmic cap or residual
budget. -/
theorem sourceComposed_cycleDispersion_le
    (P : PartialSimpleCyclePacking F.incidenceGraph
      (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
    (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
    (hQcomplete : Q.IsComplete)
    (budget : ℕ)
    (hbudget : F.incidenceCount - P.usedEdges.card ≤ budget) :
    CycleMixture.cycleDispersion F.incidenceCount
      (F.composedCycleDecomposition P Q hQcomplete).length ≤
      ((2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊ : ℕ) : ℝ) +
        ((((2 * Fintype.card F.Item : ℕ) : ℝ) -
          ((2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊ : ℕ) : ℝ)) *
          (budget : ℝ)) / F.incidenceCount := by
  simpa [sourceComposedTwoTierCycleBounds] using
    (F.sourceComposedTwoTierCycleBounds P Q hQcomplete budget hbudget).cycleDispersion_le

/-- Independently of the short/long split, every cycle in the constructed
Appendix-Lemma-10 decomposition has the source extremal `2n` cap. -/
theorem sourceComposed_cycleDispersion_le_two_mul
    (P : PartialSimpleCyclePacking F.incidenceGraph
      (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
    (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
    (hQcomplete : Q.IsComplete) :
    CycleMixture.cycleDispersion F.incidenceCount
      (F.composedCycleDecomposition P Q hQcomplete).length ≤
      ((2 * Fintype.card F.Item : ℕ) : ℝ) := by
  apply (F.composedCycleDecomposition P Q hQcomplete).cycleDispersion_le_of_forall_length_le
    (2 * Fintype.card F.Item)
  intro cycle
  cases cycle with
  | inl shortCycle =>
    rw [F.composedCycleDecomposition_length_inl]
    exact (P.length_le shortCycle).trans
      (source_shortCycle_cap_le_two_mul _ F.itemCard_two_le)
  | inr longCycle =>
    rw [F.composedCycleDecomposition_length_inr]
    exact Q.length_le longCycle

/-- The source mean statistic also has the unconditional `2n` bound from the
fully constructed two-phase packing. -/
theorem sourceComposed_cycleMean_le_two_mul
    (P : PartialSimpleCyclePacking F.incidenceGraph
      (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
    (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
    (hQcomplete : Q.IsComplete) :
    (F.composedCycleDecomposition P Q hQcomplete).cycleMean ≤
      ((2 * Fintype.card F.Item : ℕ) : ℝ) := by
  apply (F.composedCycleDecomposition P Q hQcomplete).cycleMean_le_of_forall_length_le
    (2 * Fintype.card F.Item)
  intro cycle
  cases cycle with
  | inl shortCycle =>
    rw [F.composedCycleDecomposition_length_inl]
    exact (P.length_le shortCycle).trans
      (source_shortCycle_cap_le_two_mul _ F.itemCard_two_le)
  | inr longCycle =>
    rw [F.composedCycleDecomposition_length_inr]
    exact Q.length_le longCycle

/-- The source's simplified logarithmic dispersion display is valid once the
real-log cap is below `2n` (in particular, for `n ≥ 4`).  The exact two-tier
bound above and the unconditional `2n` bound cover the excluded small case. -/
theorem sourceComposed_cycleDispersion_le_simplified_log
    (P : PartialSimpleCyclePacking F.incidenceGraph
      (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
    (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
    (hQcomplete : Q.IsComplete)
    (hbudget : F.incidenceCount - P.usedEdges.card ≤
      min (2 * Fintype.card F.Item + Fintype.card F.SetId)
        (4 * Fintype.card F.Item))
    (hnfour : 4 ≤ Fintype.card F.Item) :
    CycleMixture.cycleDispersion F.incidenceCount
      (F.composedCycleDecomposition P Q hQcomplete).length ≤
      4 * Real.logb 2 (Fintype.card F.Item) +
        (4 * (Fintype.card F.Item : ℝ) *
          (2 * (Fintype.card F.Item : ℝ) -
            4 * Real.logb 2 (Fintype.card F.Item))) /
          F.incidenceCount := by
  let n : ℕ := Fintype.card F.Item
  let L : ℝ := 2 * (⌊2 * Real.logb 2 n⌋₊ : ℝ)
  let M : ℝ := 2 * (n : ℝ)
  let r : ℝ := ((F.incidenceCount - P.usedEdges.card : ℕ) : ℝ)
  let d : ℝ := F.incidenceCount
  let x : ℝ := 4 * Real.logb 2 n
  change CycleMixture.cycleDispersion F.incidenceCount
      (F.composedCycleDecomposition P Q hQcomplete).length ≤
    x + (4 * (n : ℝ) * (M - x)) / d
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast F.incidenceCount_pos
  have hrleD : r ≤ d := by
    dsimp [r, d]
    exact_mod_cast Nat.sub_le F.incidenceCount P.usedEdges.card
  have hbudgetFour : F.incidenceCount - P.usedEdges.card ≤ 4 * n := by
    exact hbudget.trans (min_le_right _ _)
  have hrleFour : r ≤ 4 * (n : ℝ) := by
    dsimp [r]
    exact_mod_cast hbudgetFour
  have hlognonneg : 0 ≤ Real.logb 2 (n : ℝ) := by
    apply Real.logb_nonneg
    · norm_num
    · exact_mod_cast (show 1 ≤ n by omega)
  have hLleX : L ≤ x := by
    have hfloor : (⌊2 * Real.logb 2 (n : ℝ)⌋₊ : ℝ) ≤
        2 * Real.logb 2 (n : ℝ) :=
      Nat.floor_le (mul_nonneg (by positivity) hlognonneg)
    dsimp [L, x]
    nlinarith
  have hxleM : x ≤ M := by
    dsimp [x, M]
    exact four_mul_logb_le_two_mul n hnfour
  have halpha :
      CycleMixture.cycleDispersion F.incidenceCount
        (F.composedCycleDecomposition P Q hQcomplete).length ≤
      L + (M - L) * r / d := by
    dsimp [L, M, r, d, n]
    simpa [sourceComposedTwoTierCycleBounds, Nat.cast_mul] using
      (F.sourceComposedTwoTierCycleBounds P Q hQcomplete
        (F.incidenceCount - P.usedEdges.card) le_rfl).cycleDispersion_le
  have hcomparison : L + (M - L) * r / d ≤
      x + (M - x) * (4 * (n : ℝ)) / d := by
    have hnumerator : 0 ≤
        (x - L) * (d - r) + (M - x) * (4 * (n : ℝ) - r) := by
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr hLleX) (sub_nonneg.mpr hrleD))
        (mul_nonneg (sub_nonneg.mpr hxleM) (sub_nonneg.mpr hrleFour))
    have hidentity :
        (x + (M - x) * (4 * (n : ℝ)) / d) -
          (L + (M - L) * r / d) =
        ((x - L) * (d - r) + (M - x) * (4 * (n : ℝ) - r)) / d := by
      field_simp [ne_of_gt hdpos]
      ring
    rw [← sub_nonneg]
    rw [hidentity]
    exact div_nonneg hnumerator hdpos.le
  calc
    CycleMixture.cycleDispersion F.incidenceCount
        (F.composedCycleDecomposition P Q hQcomplete).length ≤
        L + (M - L) * r / d := halpha
    _ ≤ x + (M - x) * (4 * (n : ℝ)) / d := hcomparison
    _ = x + (4 * (n : ℝ) * (M - x)) / d := by ring

/-- Corrected source display for the Appendix-Lemma-10 dispersion statistic.
The `n ≥ 4` hypothesis is exactly the range in which its real-logarithmic
weakening is no larger than the independently proved `2n` bound. -/
theorem sourceComposed_cycleDispersion_le_source_min
    (P : PartialSimpleCyclePacking F.incidenceGraph
      (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
    (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
    (hQcomplete : Q.IsComplete)
    (hbudget : F.incidenceCount - P.usedEdges.card ≤
      min (2 * Fintype.card F.Item + Fintype.card F.SetId)
        (4 * Fintype.card F.Item))
    (hnfour : 4 ≤ Fintype.card F.Item) :
    CycleMixture.cycleDispersion F.incidenceCount
      (F.composedCycleDecomposition P Q hQcomplete).length ≤
      min
        (4 * Real.logb 2 (Fintype.card F.Item) +
          (4 * (Fintype.card F.Item : ℝ) *
            (2 * (Fintype.card F.Item : ℝ) -
              4 * Real.logb 2 (Fintype.card F.Item))) /
            F.incidenceCount)
        (2 * (Fintype.card F.Item : ℝ)) := by
  apply le_min
  · exact F.sourceComposed_cycleDispersion_le_simplified_log P Q hQcomplete
      hbudget hnfour
  · simpa [Nat.cast_mul] using F.sourceComposed_cycleDispersion_le_two_mul P Q hQcomplete

/-- Corrected source mean display for Appendix Lemma 10.  The positive
denominator premise is necessary: without it, the paper's printed rational
branch can be negative even though a cycle mean is positive. -/
theorem sourceComposed_cycleMean_le_source_min
    (P : PartialSimpleCyclePacking F.incidenceGraph
      (2 * ⌊2 * Real.logb 2 (Fintype.card F.Item)⌋₊))
    (Q : PartialSimpleCyclePacking P.residual (2 * Fintype.card F.Item))
    (hQcomplete : Q.IsComplete)
    (hbudget : F.incidenceCount - P.usedEdges.card ≤
      min (2 * Fintype.card F.Item + Fintype.card F.SetId)
        (4 * Fintype.card F.Item))
    (hnfour : 4 ≤ Fintype.card F.Item)
    (hden : 0 < (F.incidenceCount : ℝ) -
      4 * (Fintype.card F.Item : ℝ) +
        2 * (4 * Real.logb 2 (Fintype.card F.Item))) :
    (F.composedCycleDecomposition P Q hQcomplete).cycleMean ≤
      min
        ((F.incidenceCount : ℝ) * (4 * Real.logb 2 (Fintype.card F.Item)) /
          ((F.incidenceCount : ℝ) - 4 * (Fintype.card F.Item : ℝ) +
            2 * (4 * Real.logb 2 (Fintype.card F.Item))))
        (2 * (Fintype.card F.Item : ℝ)) := by
  let n : ℕ := Fintype.card F.Item
  let L : ℝ := 2 * (⌊2 * Real.logb 2 n⌋₊ : ℝ)
  let M : ℝ := 2 * (n : ℝ)
  let d : ℝ := F.incidenceCount
  let x : ℝ := 4 * Real.logb 2 n
  let R : ℝ := 4 * (n : ℝ)
  let A : ℝ := (d - R) / x + 2
  change (F.composedCycleDecomposition P Q hQcomplete).cycleMean ≤
    min (d * x / (d - R + 2 * x)) M
  have hnrealPos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega) hnfour)
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast F.incidenceCount_pos
  have hLleX : L ≤ x := by
    have hlognonneg : 0 ≤ Real.logb 2 (n : ℝ) := by
      apply Real.logb_nonneg
      · norm_num
      · exact_mod_cast (show 1 ≤ n by omega)
    have hfloor : (⌊2 * Real.logb 2 (n : ℝ)⌋₊ : ℝ) ≤
        2 * Real.logb 2 (n : ℝ) :=
      Nat.floor_le (mul_nonneg (by positivity) hlognonneg)
    dsimp [L, x]
    nlinarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact source_shortCycle_cap_pos n (by omega)
  have hxpos : 0 < x := hLpos.trans_le hLleX
  have hxleM : x ≤ M := by
    dsimp [x, M]
    exact four_mul_logb_le_two_mul n hnfour
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hbudgetFourNat : F.incidenceCount - P.usedEdges.card ≤ 4 * n := by
    exact hbudget.trans (min_le_right _ _)
  have hbudgetFour : F.incidenceCount - P.usedEdges.card ≤ 4 * n :=
    hbudgetFourNat
  have htwo : R / M = 2 := by
    dsimp [R, M]
    field_simp [ne_of_gt hnrealPos]
    ring
  have hmeanM : (F.composedCycleDecomposition P Q hQcomplete).cycleMean ≤ M := by
    simpa [M, n, Nat.cast_mul] using
      F.sourceComposed_cycleMean_le_two_mul P Q hQcomplete
  have hcycleCardPos : 0 <
      (Fintype.card (F.composedCycleDecomposition P Q hQcomplete).Cycle : ℝ) := by
    exact_mod_cast (F.composedCycleDecomposition P Q hQcomplete).cycle_card_pos
  have hcardM : d / M ≤
      (Fintype.card (F.composedCycleDecomposition P Q hQcomplete).Cycle : ℝ) := by
    have hmeanM' : d /
        (Fintype.card (F.composedCycleDecomposition P Q hQcomplete).Cycle : ℝ) ≤ M := by
      simpa [d] using hmeanM
    apply (div_le_iff₀ hMpos).2
    have hdle := (div_le_iff₀ hcycleCardPos).mp hmeanM'
    nlinarith
  have hBcount : (d - R) / L + R / M ≤
      (Fintype.card (F.composedCycleDecomposition P Q hQcomplete).Cycle : ℝ) := by
    simpa [sourceComposedTwoTierCycleBounds, L, M, R, d, n, Nat.cast_mul] using
      ChoiceSystem.CycleDecomposition.TwoTierCycleBounds.cycle_card_lower
        (D := F.composedCycleDecomposition P Q hQcomplete)
        (B := F.sourceComposedTwoTierCycleBounds P Q hQcomplete (4 * n) hbudgetFour)
        hLpos hMpos
  have hAcount : A ≤
      (Fintype.card (F.composedCycleDecomposition P Q hQcomplete).Cycle : ℝ) := by
    by_cases hdR : R ≤ d
    · have hquot : (d - R) / x ≤ (d - R) / L := by
        have hnum : 0 ≤ d - R := sub_nonneg.mpr hdR
        have hidentity : (d - R) / L - (d - R) / x =
            ((d - R) * (x - L)) / (L * x) := by
          field_simp [ne_of_gt hLpos, ne_of_gt hxpos]
        rw [← sub_nonneg]
        rw [hidentity]
        exact div_nonneg (mul_nonneg hnum (sub_nonneg.mpr hLleX))
          (mul_nonneg hLpos.le hxpos.le)
      calc
        A = (d - R) / x + 2 := rfl
        _ ≤ (d - R) / L + 2 := by
          simpa [add_comm] using add_le_add_right hquot 2
        _ = (d - R) / L + R / M := by rw [htwo]
        _ ≤ _ := hBcount
    · have hRd : 0 ≤ R - d := sub_nonneg.mpr (le_of_not_ge hdR)
      have hcomparison : A ≤ d / M := by
        have hidentity : d / M - A = ((R - d) * (M - x)) / (x * M) := by
          dsimp [A]
          rw [← htwo]
          field_simp [ne_of_gt hxpos, ne_of_gt hMpos]
          ring_nf
        rw [← sub_nonneg]
        rw [hidentity]
        exact div_nonneg (mul_nonneg hRd (sub_nonneg.mpr hxleM))
          (mul_nonneg hxpos.le hMpos.le)
      exact hcomparison.trans hcardM
  have hden' : 0 < d - R + 2 * x := by
    simpa [d, R, x, n] using hden
  have hAeq : A = (d - R + 2 * x) / x := by
    dsimp [A]
    field_simp [ne_of_gt hxpos]
  have hApos : 0 < A := by
    rw [hAeq]
    exact div_pos hden' hxpos
  have hmeanA : (F.composedCycleDecomposition P Q hQcomplete).cycleMean ≤ d / A :=
    (F.composedCycleDecomposition P Q hQcomplete).cycleMean_le_of_cycle_card_lower
      A hApos hAcount
  have hratio : d / A = d * x / (d - R + 2 * x) := by
    rw [hAeq]
    field_simp [ne_of_gt hxpos, ne_of_gt hden']
  apply le_min
  · exact hmeanA.trans_eq hratio
  · exact hmeanM

end ChoiceFrame

end SeshadriUgander2020IIATesting
