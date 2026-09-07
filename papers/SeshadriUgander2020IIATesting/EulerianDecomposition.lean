import SeshadriUgander2020IIATesting.EulerianCycles
import SeshadriUgander2020IIATesting.Testing
import Mathlib.Data.Set.Card

/-!
# From Eulerian incidence components to signed cycle decompositions

The source's Eulerian condition first produces two endpoint pairings.  This
module packages the remaining sign choice on their alternating components and
derives the exact `CycleDecomposition` data used by the statistical argument.
The outstanding unconditional step is the construction of this sign choice
from the two-colored even cycles themselves.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceFrame

variable {F : ChoiceFrame}

namespace Eulerian

/-- A sign orientation of the paired incidence components.  A sign flips at
both endpoints of every observation edge, precisely the local conservation
condition needed for the source perturbation family. -/
structure ComponentOrientation (h : F.Eulerian) where
  base : F.Observation → ℝ
  base_eq_one_or_neg_one : ∀ o, base o = 1 ∨ base o = -1
  set_flip : ∀ o, base (h.setMate o) = -base o
  item_flip : ∀ o, base (h.itemMate o) = -base o

namespace ComponentOrientation

variable {h : F.Eulerian} (O : ComponentOrientation h)

/-- The two advance-orbits in every alternating component receive opposite
signs.  The orbit reflection theorem from `EulerianCycles` makes this a
concrete orientation from the paper's Eulerian hypothesis alone. -/
noncomputable def canonical (h : F.Eulerian) : ComponentOrientation h where
  base := fun o => h.factorSign (h.advanceFactor o)
  base_eq_one_or_neg_one := by
    intro o
    unfold Eulerian.factorSign
    split <;> simp
  set_flip := by
    intro o
    rw [h.advanceFactor_setMate, h.factorSign_factorMate]
  item_flip := by
    intro o
    rw [h.advanceFactor_itemMate, h.factorSign_factorMate]

private theorem component_eq_of_setMate (o : F.Observation) :
    h.alternatingPairing.cycleGraph.connectedComponentMk (h.setMate o) =
      h.alternatingPairing.cycleGraph.connectedComponentMk o :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (h.alternatingPairing_cycleGraph_adj_setMate o).symm

private theorem component_eq_of_itemMate (o : F.Observation) :
    h.alternatingPairing.cycleGraph.connectedComponentMk (h.itemMate o) =
      h.alternatingPairing.cycleGraph.connectedComponentMk o :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (h.alternatingPairing_cycleGraph_adj_itemMate o).symm

private theorem componentIndex_eq_of_setMate (o : F.Observation) :
    (h.componentCycleEdgeEquiv.symm (h.setMate o)).1 =
      (h.componentCycleEdgeEquiv.symm o).1 := by
  rw [h.componentCycleEdgeEquiv_symm_fst,
    h.componentCycleEdgeEquiv_symm_fst]
  exact component_eq_of_setMate o

private theorem componentIndex_eq_of_itemMate (o : F.Observation) :
    (h.componentCycleEdgeEquiv.symm (h.itemMate o)).1 =
      (h.componentCycleEdgeEquiv.symm o).1 := by
  rw [h.componentCycleEdgeEquiv_symm_fst,
    h.componentCycleEdgeEquiv_symm_fst]
  exact component_eq_of_itemMate o

/-- The positive half of one signed incidence-cycle component. -/
def Positive (c : h.alternatingPairing.cycleGraph.ConnectedComponent) : Type :=
  {o : F.Observation //
    h.alternatingPairing.cycleGraph.connectedComponentMk o = c ∧ O.base o = 1}

private theorem advance_component (o : F.Observation) :
    h.alternatingPairing.cycleGraph.connectedComponentMk (h.advancePerm o) =
      h.alternatingPairing.cycleGraph.connectedComponentMk o := by
  rw [h.advancePerm_apply]
  calc
    h.alternatingPairing.cycleGraph.connectedComponentMk
        (h.itemMate (h.setMate o)) =
        h.alternatingPairing.cycleGraph.connectedComponentMk (h.setMate o) :=
      component_eq_of_itemMate (h.setMate o)
    _ = h.alternatingPairing.cycleGraph.connectedComponentMk o :=
      component_eq_of_setMate o

private theorem advance_base (o : F.Observation) :
    O.base (h.advancePerm o) = O.base o := by
  rw [h.advancePerm_apply, O.item_flip, O.set_flip]
  ring

/-- Advancing through a choice-set pairing and then an item pairing permutes
the positive observations of each component. -/
noncomputable def positiveSuccessor
    (c : h.alternatingPairing.cycleGraph.ConnectedComponent) :
    Equiv.Perm (O.Positive c) where
  toFun := fun v =>
    ⟨h.advancePerm v.1, by
      exact ⟨(advance_component v.1).trans v.2.1,
        (advance_base (O := O) v.1).trans v.2.2⟩⟩
  invFun := fun v =>
    ⟨h.setMate (h.itemMate v.1), by
      refine ⟨(component_eq_of_setMate (h.itemMate v.1)).trans
        ((component_eq_of_itemMate v.1).trans v.2.1), ?_⟩
      calc
        O.base (h.setMate (h.itemMate v.1)) = -O.base (h.itemMate v.1) :=
          O.set_flip _
        _ = -(-O.base v.1) := by rw [O.item_flip]
        _ = O.base v.1 := by ring
        _ = 1 := v.2.2⟩
  left_inv := by
    rintro ⟨o, ho⟩
    apply Subtype.ext
    change h.setMate (h.itemMate (h.itemMate (h.setMate o))) = o
    rw [h.itemMate_apply_apply, h.setMate_apply_apply]
  right_inv := by
    rintro ⟨o, ho⟩
    apply Subtype.ext
    change h.itemMate (h.setMate (h.setMate (h.itemMate o))) = o
    rw [h.setMate_apply_apply, h.itemMate_apply_apply]

/-- The finite position indices of one connected component are equivalent to
the observations lying in that component. -/
noncomputable def componentPositionEquiv
    (c : h.alternatingPairing.cycleGraph.ConnectedComponent) :
    Fin c.supp.ncard ≃ {o : F.Observation //
      h.alternatingPairing.cycleGraph.connectedComponentMk o = c} where
  toFun := fun i => ⟨h.componentCycleEdgeEquiv ⟨c, i⟩, by
    have hindex := congrArg Sigma.fst
      (h.componentCycleEdgeEquiv.symm_apply_apply ⟨c, i⟩)
    rw [h.componentCycleEdgeEquiv_symm_fst] at hindex
    exact hindex⟩
  invFun := fun o => ⟨(h.componentCycleEdgeEquiv.symm o.1).2.1, by
    have hindex := h.componentCycleEdgeEquiv_symm_fst o.1
    rw [o.2] at hindex
    simpa [hindex] using (h.componentCycleEdgeEquiv.symm o.1).2.2⟩
  left_inv := by
    intro i
    apply Fin.ext
    change (h.componentCycleEdgeEquiv.symm
      (h.componentCycleEdgeEquiv ⟨c, i⟩)).2.1 = i.1
    rw [h.componentCycleEdgeEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨o, ho⟩
    apply Subtype.ext
    let z := h.componentCycleEdgeEquiv.symm o
    have hzindex : z.1 = c := by
      simpa [z, ho] using h.componentCycleEdgeEquiv_symm_fst o
    have hzpair :
        (⟨c, ⟨z.2.1, by simpa [hzindex] using z.2.2⟩⟩ :
          Σ c : h.alternatingPairing.cycleGraph.ConnectedComponent,
            Fin c.supp.ncard) = z := by
      cases hzindex
      rfl
    have hzapply : h.componentCycleEdgeEquiv
        ⟨c, ⟨z.2.1, by simpa [hzindex] using z.2.2⟩⟩ = o := by
      rw [hzpair]
      exact h.componentCycleEdgeEquiv.apply_symm_apply o
    exact hzapply

/-- Each component is the disjoint union of its positive observations and
their choice-set-paired negative observations. -/
noncomputable def positiveEdgeEquiv
    (c : h.alternatingPairing.cycleGraph.ConnectedComponent) :
    O.Positive c × Bool ≃ {o : F.Observation //
      h.alternatingPairing.cycleGraph.connectedComponentMk o = c} where
  toFun := fun p =>
    match p.2 with
    | false => ⟨p.1.1, p.1.2.1⟩
    | true => ⟨h.setMate p.1.1,
      (component_eq_of_setMate p.1.1).trans p.1.2.1⟩
  invFun := fun o =>
    if hpos : O.base o.1 = 1 then
      (⟨o.1, ⟨o.2, hpos⟩⟩, false)
    else
      (⟨h.setMate o.1, by
        refine ⟨(component_eq_of_setMate o.1).trans o.2, ?_⟩
        rcases O.base_eq_one_or_neg_one o.1 with hbase | hbase
        · exact (hpos hbase).elim
        · rw [O.set_flip, hbase]
          norm_num⟩, true)
  left_inv := by
    rintro ⟨v, b⟩
    cases b with
    | false =>
      simp only [v.2.2, ↓reduceDIte]
      rfl
    | true =>
      have hnot : ¬ O.base (h.setMate v.1) = 1 := by
        rw [O.set_flip, v.2.2]
        norm_num
      simp only [hnot, ↓reduceDIte]
      apply Prod.ext
      · apply Subtype.ext
        exact h.setMate_apply_apply v.1
      · rfl
  right_inv := by
    rintro ⟨o, ho⟩
    by_cases hpos : O.base o = 1
    · simp only [hpos, ↓reduceDIte]
    · rcases O.base_eq_one_or_neg_one o with hbase | hbase
      · exact (hpos hbase).elim
      · simp only [hpos, ↓reduceDIte]
        apply Subtype.ext
        exact h.setMate_apply_apply o

/-- A component position first identifies the incidence edge and then records
whether it is the positive edge of a traversal vertex or its set-paired
negative companion. -/
noncomputable def edgeParamEquiv
    (c : h.alternatingPairing.cycleGraph.ConnectedComponent) :
    Fin c.supp.ncard ≃ O.Positive c × Bool :=
  (componentPositionEquiv (h := h) c).trans (O.positiveEdgeEquiv c).symm

private theorem componentCycleEdge_edgeParamEquiv_false
    (c : h.alternatingPairing.cycleGraph.ConnectedComponent) (v : O.Positive c) :
    h.componentCycleEdgeEquiv ⟨c, (O.edgeParamEquiv c).symm (v, false)⟩ = v.1 := by
  change ((componentPositionEquiv (h := h) c)
    ((componentPositionEquiv (h := h) c).symm
      (O.positiveEdgeEquiv c (v, false)))).1 = v.1
  rw [(componentPositionEquiv (h := h) c).apply_symm_apply]
  rfl

private theorem componentCycleEdge_edgeParamEquiv_true
    (c : h.alternatingPairing.cycleGraph.ConnectedComponent) (v : O.Positive c) :
    h.componentCycleEdgeEquiv ⟨c, (O.edgeParamEquiv c).symm (v, true)⟩ =
      h.setMate v.1 := by
  change ((componentPositionEquiv (h := h) c)
    ((componentPositionEquiv (h := h) c).symm
      (O.positiveEdgeEquiv c (v, true)))).1 =
      h.setMate v.1
  rw [(componentPositionEquiv (h := h) c).apply_symm_apply]
  rfl

/-- A component orientation gives the exact edge partition and balance
certificates used by source Lemmas 2--4. -/
noncomputable def cycleDecomposition : ChoiceSystem.CycleDecomposition F := by
  classical
  let G := h.alternatingPairing.cycleGraph
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  exact
    { Cycle := G.ConnectedComponent
      instFintypeCycle := inferInstance
      instDecidableEqCycle := Classical.decEq _
      length := fun c => c.supp.ncard
      length_pos := by
        intro c
        exact c.nonempty_supp.ncard_pos
      edgeEquiv := h.componentCycleEdgeEquiv
      base := O.base
      base_eq_one_or_neg_one := O.base_eq_one_or_neg_one
      set_balance := by
        intro a C
        let p := setPairing F h C
        let f : {x : F.Item // x ∈ F.members C} → ℝ := fun x =>
          O.base ⟨C, x⟩ *
            Rademacher.sign (a (h.componentCycleEdgeEquiv.symm ⟨C, x⟩).1)
        apply AppliedModelingLib.Foundations.Graph.EvenPairing.sum_eq_zero_of_apply_neg p f
        intro x
        have hindex :
            (h.componentCycleEdgeEquiv.symm (h.setMate ⟨C, x⟩)).1 =
              (h.componentCycleEdgeEquiv.symm ⟨C, x⟩).1 :=
          componentIndex_eq_of_setMate ⟨C, x⟩
        change O.base (h.setMate ⟨C, x⟩) *
            Rademacher.sign
              (a (h.componentCycleEdgeEquiv.symm (h.setMate ⟨C, x⟩)).1) =
            -(O.base ⟨C, x⟩ *
              Rademacher.sign (a (h.componentCycleEdgeEquiv.symm ⟨C, x⟩).1))
        rw [O.set_flip, hindex]
        ring
      item_balance := by
        intro a x
        let p := itemPairing F h x
        let f : {C : F.SetId // x ∈ F.members C} → ℝ := fun C =>
          O.base ⟨C.1, ⟨x, C.2⟩⟩ *
            Rademacher.sign
              (a (h.componentCycleEdgeEquiv.symm ⟨C.1, ⟨x, C.2⟩⟩).1)
        apply AppliedModelingLib.Foundations.Graph.EvenPairing.sum_eq_zero_of_apply_neg p f
        intro C
        have hindex :
            (h.componentCycleEdgeEquiv.symm
              (h.itemMate ⟨C.1, ⟨x, C.2⟩⟩)).1 =
              (h.componentCycleEdgeEquiv.symm ⟨C.1, ⟨x, C.2⟩⟩).1 :=
          componentIndex_eq_of_itemMate ⟨C.1, ⟨x, C.2⟩⟩
        change O.base (h.itemMate ⟨C.1, ⟨x, C.2⟩⟩) *
            Rademacher.sign
              (a (h.componentCycleEdgeEquiv.symm
                (h.itemMate ⟨C.1, ⟨x, C.2⟩⟩)).1) =
            -(O.base ⟨C.1, ⟨x, C.2⟩⟩ *
              Rademacher.sign
                (a (h.componentCycleEdgeEquiv.symm ⟨C.1, ⟨x, C.2⟩⟩).1))
        rw [O.item_flip, hindex]
        ring }

/-- The oriented positive incidences traverse every component by taking its
set-paired edge followed by its item-paired edge.  Together with the negative
set-paired companions, this is the explicit alternating witness required by
the paper's Lemma 2. -/
noncomputable def alternatingCycleWitness :
    (O.cycleDecomposition).AlternatingCycleWitness := by
  classical
  exact
    { Vertex := O.Positive
      instFintypeVertex := fun c => by
        letI : DecidablePred (fun o : F.Observation =>
          h.alternatingPairing.cycleGraph.connectedComponentMk o = c ∧ O.base o = 1) :=
          Classical.decPred _
        refine Fintype.subtype (Finset.univ.filter fun o : F.Observation =>
          h.alternatingPairing.cycleGraph.connectedComponentMk o = c ∧ O.base o = 1) ?_
        intro o
        simp
      instDecidableEqVertex := fun _ => Classical.decEq _
      successor := O.positiveSuccessor
      setAt := fun _ v => v.1.1
      itemAt := fun _ v => v.1.2.1
      current_mem := fun _ v => v.1.2.2
      successor_mem := by
        intro c v
        change (h.advancePerm v.1).2.1 ∈ F.members v.1.1
        rw [h.advancePerm_apply, h.itemMate_item]
        simpa only [h.setMate_fst] using (h.setMate v.1).2.2
      edgeParamEquiv := O.edgeParamEquiv
      false_edge := by
        intro c v
        change h.componentCycleEdgeEquiv
          ⟨c, (O.edgeParamEquiv c).symm (v, false)⟩ = v.1
        exact componentCycleEdge_edgeParamEquiv_false (O := O) c v
      true_edge := by
        intro c v
        change h.componentCycleEdgeEquiv
          ⟨c, (O.edgeParamEquiv c).symm (v, true)⟩ = h.setMate v.1
        exact componentCycleEdge_edgeParamEquiv_true (O := O) c v
      base_false := by
        intro c v
        change O.base (h.componentCycleEdgeEquiv
          ⟨c, (O.edgeParamEquiv c).symm (v, false)⟩) = 1
        rw [componentCycleEdge_edgeParamEquiv_false (O := O) c v]
        exact v.2.2
      base_true := by
        intro c v
        change O.base (h.componentCycleEdgeEquiv
          ⟨c, (O.edgeParamEquiv c).symm (v, true)⟩) = -1
        rw [componentCycleEdge_edgeParamEquiv_true (O := O) c v, O.set_flip, v.2.2] }

end ComponentOrientation

/-- The canonical cycle decomposition obtained directly from the Eulerian
incidence condition. -/
noncomputable def cycleDecompositionOfEulerian (h : F.Eulerian) :
    ChoiceSystem.CycleDecomposition F :=
  (ComponentOrientation.canonical h).cycleDecomposition

/-- The concrete alternating traversal for the canonical Eulerian
decomposition. -/
noncomputable def alternatingCycleWitnessOfEulerian (h : F.Eulerian) :
    (h.cycleDecompositionOfEulerian).AlternatingCycleWitness := by
  simpa only [cycleDecompositionOfEulerian] using
    (ComponentOrientation.canonical h).alternatingCycleWitness

/-- Source Lemma 2 without an additional cycle-decomposition certificate:
the Eulerian hypothesis itself constructs the signed alternating cycles. -/
theorem orientedSign_separatedFromIIA_of_eulerian (h : F.Eulerian)
    (a : h.cycleDecompositionOfEulerian.Cycle → Bool) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    ChoiceSystem.SeparatedFromIIA
      (ChoiceSystem.perturb (h.cycleDecompositionOfEulerian.orientedSign a)
        ε hε_nonneg hε_le_one)
      (ε * (Fintype.card h.cycleDecompositionOfEulerian.Cycle : ℝ) /
        (2 * (F.incidenceCount : ℝ))) :=
  ChoiceSystem.CycleDecomposition.AlternatingCycleWitness.orientedSign_separatedFromIIA
    (D := h.cycleDecompositionOfEulerian)
    h.alternatingCycleWitnessOfEulerian a ε hε_nonneg hε_le_one

/-- Source Theorem 1 in the paper's cycle-statistic notation, with the
decomposition and traversal now derived from the Eulerian assumption. -/
theorem theorem1_productTestingLowerBound_of_eulerian (h : F.Eulerian)
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * h.cycleDecompositionOfEulerian.cycleMean * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := F) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * h.cycleDecompositionOfEulerian.cycleMean ^ 4 *
              CycleMixture.cycleDispersion F.incidenceCount
                h.cycleDecompositionOfEulerian.length * (N : ℝ) ^ 2 * δ ^ 4) /
            (F.incidenceCount : ℝ)) - 1)) :=
  ChoiceSystem.CycleDecomposition.theorem1_productTestingLowerBound
    (D := h.cycleDecompositionOfEulerian)
    h.alternatingCycleWitnessOfEulerian δ hδ_nonneg hsmall N

end Eulerian

end ChoiceFrame

end SeshadriUgander2020IIATesting
