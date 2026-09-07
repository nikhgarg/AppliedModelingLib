import SeshadriUgander2020IIATesting.ChoiceSystem
import AppliedModelingLib.Foundations.Graph.AlternatingPairing

/-!
# Incidence pairings for Eulerian choice frames

For an Eulerian comparison-incidence graph, pair the incident edges at every
choice-set vertex and at every item vertex. Alternating the two pairings is
the concrete edge traversal underlying an Eulerian cycle decomposition. This
module establishes the local permutation facts; the subsequent module will
partition their finite alternating orbits into the source's simple cycles.
-/

namespace SeshadriUgander2020IIATesting

namespace ChoiceFrame

variable {F : ChoiceFrame}

namespace Eulerian

/-- The edge paired with an incidence at its choice-set endpoint. -/
noncomputable def setMate (h : F.Eulerian) (o : F.Observation) : F.Observation :=
  ⟨o.1, (setPairing F h o.1).perm o.2⟩

/-- The edge paired with an incidence at its item endpoint. -/
noncomputable def itemMate (h : F.Eulerian) (o : F.Observation) : F.Observation :=
  let C' := (itemPairing F h o.2.1).perm ⟨o.1, o.2.2⟩
  ⟨C'.1, ⟨o.2.1, C'.2⟩⟩

theorem setMate_fst (h : F.Eulerian) (o : F.Observation) :
    (h.setMate o).1 = o.1 := rfl

theorem itemMate_item (h : F.Eulerian) (o : F.Observation) :
    (h.itemMate o).2.1 = o.2.1 := rfl

theorem setMate_apply_apply (h : F.Eulerian) (o : F.Observation) :
    h.setMate (h.setMate o) = o := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact congrArg Subtype.val ((setPairing F h o.1).apply_apply o.2)

theorem setMate_ne (h : F.Eulerian) (o : F.Observation) : h.setMate o ≠ o := by
  intro heq
  apply (setPairing F h o.1).apply_ne o.2
  apply Subtype.ext
  exact congrArg (fun q : F.Observation => q.2.1) heq

theorem itemMate_apply_apply (h : F.Eulerian) (o : F.Observation) :
    h.itemMate (h.itemMate o) = o := by
  rcases o with ⟨C, x, hx⟩
  let p := itemPairing F h x
  let Cx : {D : F.SetId // x ∈ F.members D} := ⟨C, hx⟩
  let embed : {D : F.SetId // x ∈ F.members D} → F.Observation :=
    fun D => ⟨D.1, ⟨x, D.2⟩⟩
  have hp : p.perm (p.perm Cx) = Cx := p.apply_apply Cx
  calc
    h.itemMate (h.itemMate ⟨C, ⟨x, hx⟩⟩) = embed (p.perm (p.perm Cx)) := by
      rfl
    _ = embed Cx := congrArg embed hp
    _ = ⟨C, ⟨x, hx⟩⟩ := rfl

theorem itemMate_ne (h : F.Eulerian) (o : F.Observation) : h.itemMate o ≠ o := by
  intro heq
  apply (itemPairing F h o.2.1).apply_ne ⟨o.1, o.2.2⟩
  apply Subtype.ext
  exact congrArg Sigma.fst heq

/-- The two endpoint pairings never use the same partner edge.  Equality
would preserve both the choice-set and item coordinates and hence contradict
the fixed-point-free choice-set pairing. -/
theorem setMate_ne_itemMate (h : F.Eulerian) (o : F.Observation) :
    h.setMate o ≠ h.itemMate o := by
  intro heq
  apply h.setMate_ne o
  apply Sigma.ext
  · exact h.setMate_fst o
  · apply heq_of_eq
    apply Subtype.ext
    calc
      (h.setMate o).2.1 = (h.itemMate o).2.1 :=
        congrArg (fun q : F.Observation => q.2.1) heq
      _ = o.2.1 := h.itemMate_item o

/-- The fixed-point-free involution pairing edges at choice-set endpoints. -/
noncomputable def setPerm (h : F.Eulerian) : Equiv.Perm F.Observation where
  toFun := h.setMate
  invFun := h.setMate
  left_inv := h.setMate_apply_apply
  right_inv := h.setMate_apply_apply

/-- The fixed-point-free involution pairing edges at item endpoints. -/
noncomputable def itemPerm (h : F.Eulerian) : Equiv.Perm F.Observation where
  toFun := h.itemMate
  invFun := h.itemMate
  left_inv := h.itemMate_apply_apply
  right_inv := h.itemMate_apply_apply

/-- The choice-set endpoint involution as a reusable even pairing. -/
noncomputable def setEvenPairing (h : F.Eulerian) :
    AppliedModelingLib.Foundations.Graph.EvenPairing F.Observation where
  perm := h.setPerm
  apply_apply := h.setMate_apply_apply
  apply_ne := h.setMate_ne

/-- The item endpoint involution as a reusable even pairing. -/
noncomputable def itemEvenPairing (h : F.Eulerian) :
    AppliedModelingLib.Foundations.Graph.EvenPairing F.Observation where
  perm := h.itemPerm
  apply_apply := h.itemMate_apply_apply
  apply_ne := h.itemMate_ne

/-- The 2-regular incidence graph induced by the two endpoint pairings.
Its connected components are the alternating cycle pieces needed for the
source's Eulerian cycle decomposition. -/
noncomputable def alternatingPairing (h : F.Eulerian) :
    AppliedModelingLib.Foundations.Graph.AlternatingPairing F.Observation where
  first := h.setEvenPairing
  second := h.itemEvenPairing
  distinct := h.setMate_ne_itemMate

theorem alternatingPairing_cycleGraph_isCycles (h : F.Eulerian) :
    h.alternatingPairing.cycleGraph.IsCycles :=
  h.alternatingPairing.cycleGraph_isCycles

/-- The cycle graph's edges alternate between choice-set and item endpoint
pairings; this retains the bicoloring needed to orient each component. -/
theorem alternatingPairing_cycleGraph_isAlternatingSet (h : F.Eulerian) :
    h.alternatingPairing.cycleGraph.IsAlternating
      (AppliedModelingLib.Foundations.Graph.AlternatingPairing.matchingSubgraph
        h.setEvenPairing).spanningCoe :=
  h.alternatingPairing.cycleGraph_isAlternatingFirst

theorem alternatingPairing_cycleGraph_adj_setMate (h : F.Eulerian)
    (o : F.Observation) :
    h.alternatingPairing.cycleGraph.Adj o (h.setMate o) :=
  h.alternatingPairing.cycleGraph_adj_first o

theorem alternatingPairing_cycleGraph_adj_itemMate (h : F.Eulerian)
    (o : F.Observation) :
    h.alternatingPairing.cycleGraph.Adj o (h.itemMate o) :=
  h.alternatingPairing.cycleGraph_adj_second o

/-- Every observation lies on a simple component cycle in the two-colored
incidence graph. This is the raw graph-theoretic form of the source's
Eulerian cycle-decomposition step. -/
theorem exists_component_cycle (h : F.Eulerian) (o : F.Observation) :
    ∃ (p : h.alternatingPairing.cycleGraph.Walk o o), p.IsCycle ∧
      p.toSubgraph.verts =
        (h.alternatingPairing.cycleGraph.connectedComponentMk o).supp := by
  exact SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    h.alternatingPairing_cycleGraph_isCycles
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    (h.alternatingPairing.cycleGraph_neighbors_nonempty o)

/-- The raw source edge partition: a component index together with a finite
position in that component enumerates every observation exactly once. -/
noncomputable def componentCycleEdgeEquiv (h : F.Eulerian) :
    (Σ c : h.alternatingPairing.cycleGraph.ConnectedComponent,
      Fin c.supp.ncard) ≃ F.Observation :=
  AppliedModelingLib.Foundations.Graph.AlternatingPairing.componentIndexEquiv
    h.alternatingPairing.cycleGraph

theorem componentCycleEdgeEquiv_symm_fst (h : F.Eulerian) (o : F.Observation) :
    (h.componentCycleEdgeEquiv.symm o).1 =
      h.alternatingPairing.cycleGraph.connectedComponentMk o :=
  AppliedModelingLib.Foundations.Graph.AlternatingPairing.componentIndexEquiv_symm_fst
    h.alternatingPairing.cycleGraph o

/-- Advance along one set-pairing and then one item-pairing. Its finite
orbits are the two alternating edge classes of the source cycles. -/
noncomputable def advancePerm (h : F.Eulerian) : Equiv.Perm F.Observation :=
  (h.setPerm).trans h.itemPerm

theorem advancePerm_apply (h : F.Eulerian) (o : F.Observation) :
    h.advancePerm o = h.itemMate (h.setMate o) := rfl

theorem setPerm_inv (h : F.Eulerian) : (h.setPerm)⁻¹ = h.setPerm := by
  ext o
  rfl

theorem itemPerm_inv (h : F.Eulerian) : (h.itemPerm)⁻¹ = h.itemPerm := by
  ext o
  rfl

theorem advancePerm_eq_mul (h : F.Eulerian) :
    h.advancePerm = h.itemPerm * h.setPerm := rfl

/-- Reversing a source cycle corresponds to conjugating its two-step edge
advance by the choice-set pairing. -/
theorem setPerm_conj_advancePerm (h : F.Eulerian) :
    h.setPerm * h.advancePerm * (h.setPerm)⁻¹ = (h.advancePerm)⁻¹ := by
  have hset_sq : h.setPerm * h.setPerm = 1 := by
    rw [← h.setPerm_inv]
    exact mul_inv_cancel _
  calc
    h.setPerm * h.advancePerm * (h.setPerm)⁻¹ =
        h.setPerm * (h.itemPerm * h.setPerm) * h.setPerm := by
      rw [h.advancePerm_eq_mul, h.setPerm_inv]
    _ = h.setPerm * h.itemPerm := by
      calc
        h.setPerm * (h.itemPerm * h.setPerm) * h.setPerm =
            h.setPerm * h.itemPerm * (h.setPerm * h.setPerm) := by
          group
        _ = h.setPerm * h.itemPerm := by rw [hset_sq, mul_one]
    _ = (h.advancePerm)⁻¹ := by
      rw [h.advancePerm_eq_mul, mul_inv_rev, h.setPerm_inv, h.itemPerm_inv]

/-- Inverting every cyclic factor gives a cyclic factor of the inverse
permutation. -/
theorem inv_mem_cycleFactorsFinset_inv {α : Type*} [Fintype α] [DecidableEq α]
    {f c : Equiv.Perm α} (hc : c ∈ f.cycleFactorsFinset) :
    c⁻¹ ∈ (f⁻¹).cycleFactorsFinset := by
  rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc ⊢
  refine ⟨hc.1.inv, ?_⟩
  intro a ha
  have hcsupport : c⁻¹ a ∈ c.support := by
    rw [Equiv.Perm.mem_support]
    simpa using (Equiv.Perm.mem_support.mp ha).symm
  apply f.injective
  calc
    f (c⁻¹ a) = c (c⁻¹ a) := (hc.2 _ hcsupport).symm
    _ = a := c.apply_symm_apply a
    _ = f (f⁻¹ a) := (f.apply_symm_apply a).symm

/-- Choice-set reflection maps an advance-cycle factor to its partner factor.
The next orbit-selection step will choose one of this pair as the false-edge
class of a source cycle. -/
noncomputable def factorMate (h : F.Eulerian)
    (c : h.advancePerm.cycleFactorsFinset) : h.advancePerm.cycleFactorsFinset := by
  let a := h.setPerm
  let f := h.advancePerm
  refine ⟨a * (c : Equiv.Perm F.Observation)⁻¹ * a⁻¹, ?_⟩
  have hc_inv : (c : Equiv.Perm F.Observation)⁻¹ ∈ (f⁻¹).cycleFactorsFinset :=
    inv_mem_cycleFactorsFinset_inv c.2
  have hconj_inv : a * f⁻¹ * a⁻¹ = f := by
    calc
      a * f⁻¹ * a⁻¹ = (a * f * a⁻¹)⁻¹ := by group
      _ = (f⁻¹)⁻¹ := by rw [show a * f * a⁻¹ = f⁻¹ from h.setPerm_conj_advancePerm]
      _ = f := inv_inv _
  have hmem := (Equiv.Perm.mem_cycleFactorsFinset_conj f⁻¹ a
    ((c : Equiv.Perm F.Observation)⁻¹)).mpr hc_inv
  rw [hconj_inv] at hmem
  exact hmem

theorem factorMate_apply_apply (h : F.Eulerian)
    (c : h.advancePerm.cycleFactorsFinset) : h.factorMate (h.factorMate c) = c := by
  apply Subtype.ext
  have hset_sq : h.setPerm * h.setPerm = 1 := by
    rw [← h.setPerm_inv]
    exact mul_inv_cancel _
  simp only [factorMate, h.setPerm_inv]
  rw [mul_inv_rev, mul_inv_rev, inv_inv, h.setPerm_inv]
  calc
    h.setPerm * (h.setPerm * (c : Equiv.Perm F.Observation) * h.setPerm) *
        h.setPerm =
        (h.setPerm * h.setPerm) * (c : Equiv.Perm F.Observation) *
          (h.setPerm * h.setPerm) := by simp only [mul_assoc]
    _ = c := by rw [hset_sq]; simp

/-- Choice-set reflection transports the support of an advance factor to the
support of its reflected factor. -/
theorem setPerm_mem_factorMate_support (h : F.Eulerian)
    (c : h.advancePerm.cycleFactorsFinset) (x : F.Observation)
    (hx : x ∈ (c : Equiv.Perm F.Observation).support) :
    h.setPerm x ∈ (h.factorMate c : Equiv.Perm F.Observation).support := by
  have hcinv_ne : (c : Equiv.Perm F.Observation)⁻¹ x ≠ x := by
    intro heq
    apply Equiv.Perm.mem_support.mp hx
    calc
      (c : Equiv.Perm F.Observation) x =
          (c : Equiv.Perm F.Observation) ((c : Equiv.Perm F.Observation)⁻¹ x) := by
        rw [heq]
      _ = x := (c : Equiv.Perm F.Observation).apply_symm_apply x
  rw [Equiv.Perm.mem_support]
  change (h.setPerm * (c : Equiv.Perm F.Observation)⁻¹ * (h.setPerm)⁻¹)
      (h.setPerm x) ≠ h.setPerm x
  rw [h.setPerm_inv]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [show h.setPerm (h.setPerm x) = x from h.setMate_apply_apply x]
  exact fun hfix => hcinv_ne (h.setPerm.injective hfix)

/-- The two alternating edge classes of a component are distinct advance
orbits.  Otherwise the choice-set reflection would be an odd reflection of a
single orbit: an even reflection fixes a choice-set pairing edge and an odd
reflection fixes an item pairing edge, contradicting that both pairings are
fixed-point-free. -/
theorem factorMate_ne (h : F.Eulerian)
    (c : h.advancePerm.cycleFactorsFinset) : h.factorMate c ≠ c := by
  classical
  intro hself
  have hself' : h.setPerm * (c : Equiv.Perm F.Observation)⁻¹ * (h.setPerm)⁻¹ = c := by
    have hself_val := congrArg Subtype.val hself
    simpa only [factorMate] using hself_val
  have hconj : h.setPerm * (c : Equiv.Perm F.Observation) * (h.setPerm)⁻¹ =
      (c : Equiv.Perm F.Observation)⁻¹ := by
    calc
      h.setPerm * (c : Equiv.Perm F.Observation) * (h.setPerm)⁻¹ =
          (h.setPerm * (c : Equiv.Perm F.Observation)⁻¹ * (h.setPerm)⁻¹)⁻¹ := by
        group
      _ = (c : Equiv.Perm F.Observation)⁻¹ := by rw [hself']
  have hcomm : h.setPerm * (c : Equiv.Perm F.Observation) =
      (c : Equiv.Perm F.Observation)⁻¹ * h.setPerm := by
    calc
      h.setPerm * (c : Equiv.Perm F.Observation) =
          (h.setPerm * (c : Equiv.Perm F.Observation) * (h.setPerm)⁻¹) * h.setPerm := by
        group
      _ = (c : Equiv.Perm F.Observation)⁻¹ * h.setPerm := by rw [hconj]
  have hcomm_pow : ∀ n : ℕ,
      h.setPerm * (c : Equiv.Perm F.Observation) ^ n =
        ((c : Equiv.Perm F.Observation)⁻¹) ^ n * h.setPerm := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc
        h.setPerm * ((c : Equiv.Perm F.Observation) ^ n * c) =
            (h.setPerm * (c : Equiv.Perm F.Observation) ^ n) * c := by group
        _ = (((c : Equiv.Perm F.Observation)⁻¹ ^ n) * h.setPerm) * c := by rw [ih]
        _ = ((c : Equiv.Perm F.Observation)⁻¹) ^ n *
            (h.setPerm * c) := by group
        _ = ((c : Equiv.Perm F.Observation)⁻¹) ^ n *
            ((c : Equiv.Perm F.Observation)⁻¹ * h.setPerm) := by rw [hcomm]
        _ = ((c : Equiv.Perm F.Observation)⁻¹) ^ (n + 1) * h.setPerm := by
          rw [pow_succ]
          group
  have hc := Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2
  obtain ⟨x, hx⟩ := Equiv.Perm.IsCycle.nonempty_support hc.1
  have hax : h.setPerm x ∈ (c : Equiv.Perm F.Observation).support := by
    have h := h.setPerm_mem_factorMate_support c x hx
    rwa [hself] at h
  obtain ⟨k, hk⟩ := hc.1.exists_pow_eq
    (Equiv.Perm.mem_support.mp hx) (Equiv.Perm.mem_support.mp hax)
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · obtain ⟨n, hn⟩ := hk_even
    have hkn : k = n + n := by omega
    have hfixed : h.setPerm (((c : Equiv.Perm F.Observation) ^ n) x) =
        ((c : Equiv.Perm F.Observation) ^ n) x := by
      change (h.setPerm * (c : Equiv.Perm F.Observation) ^ n) x =
        ((c : Equiv.Perm F.Observation) ^ n) x
      rw [hcomm_pow n]
      rw [inv_pow]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have hpower : (c : Equiv.Perm F.Observation) ^ (n + n) =
          (c : Equiv.Perm F.Observation) ^ n * (c : Equiv.Perm F.Observation) ^ n :=
        pow_add _ _ _
      rw [← hk, hkn, hpower]
      change (((c : Equiv.Perm F.Observation) ^ n)⁻¹ *
        ((c : Equiv.Perm F.Observation) ^ n * (c : Equiv.Perm F.Observation) ^ n)) x =
          ((c : Equiv.Perm F.Observation) ^ n) x
      congr 1
      group
    exact h.setMate_ne _ (by simpa [setPerm] using hfixed)
  · obtain ⟨n, hn⟩ := hk_odd
    have hkn : k = (n + 1) + n := by omega
    have hay : h.setPerm (((c : Equiv.Perm F.Observation) ^ (n + 1)) x) =
        ((c : Equiv.Perm F.Observation) ^ n) x := by
      change (h.setPerm * (c : Equiv.Perm F.Observation) ^ (n + 1)) x =
        ((c : Equiv.Perm F.Observation) ^ n) x
      rw [hcomm_pow (n + 1)]
      rw [inv_pow]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      have hpower : (c : Equiv.Perm F.Observation) ^ ((n + 1) + n) =
          (c : Equiv.Perm F.Observation) ^ (n + 1) *
            (c : Equiv.Perm F.Observation) ^ n := pow_add _ _ _
      rw [← hk, hkn, hpower]
      change (((c : Equiv.Perm F.Observation) ^ (n + 1))⁻¹ *
        ((c : Equiv.Perm F.Observation) ^ (n + 1) *
          (c : Equiv.Perm F.Observation) ^ n)) x =
            ((c : Equiv.Perm F.Observation) ^ n) x
      congr 1
      group
    have hxn : ((c : Equiv.Perm F.Observation) ^ n) x ∈
        (c : Equiv.Perm F.Observation).support :=
      Equiv.Perm.pow_apply_mem_support.2 hx
    have hadvance : h.advancePerm (((c : Equiv.Perm F.Observation) ^ n) x) =
        (c : Equiv.Perm F.Observation) (((c : Equiv.Perm F.Observation) ^ n) x) :=
      (hc.2 _ hxn).symm
    have hitem : h.itemPerm (((c : Equiv.Perm F.Observation) ^ (n + 1)) x) =
        ((c : Equiv.Perm F.Observation) ^ (n + 1)) x := by
      change (h.itemPerm * (c : Equiv.Perm F.Observation) ^ (n + 1)) x =
        ((c : Equiv.Perm F.Observation) ^ (n + 1)) x
      have hset_sq : h.setPerm * h.setPerm = 1 := by
        rw [← h.setPerm_inv]
        exact mul_inv_cancel _
      have hitem_eq : h.itemPerm = h.advancePerm * h.setPerm := by
        calc
          h.itemPerm = h.itemPerm * (h.setPerm * h.setPerm) := by rw [hset_sq, mul_one]
          _ = (h.itemPerm * h.setPerm) * h.setPerm := by group
          _ = h.advancePerm * h.setPerm := by rw [h.advancePerm_eq_mul]
      rw [hitem_eq]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, hay, hadvance]
      rw [pow_succ]
      change ((c : Equiv.Perm F.Observation) *
        (c : Equiv.Perm F.Observation) ^ n) x =
          ((c : Equiv.Perm F.Observation) ^ n * c) x
      congr 1
      group
    exact h.itemMate_ne _ (by simpa [itemPerm] using hitem)

theorem advancePerm_ne (h : F.Eulerian) (o : F.Observation) :
    h.advancePerm o ≠ o := by
  intro heq
  apply h.setMate_ne o
  apply Sigma.ext
  · exact h.setMate_fst o
  · apply heq_of_eq
    apply Subtype.ext
    have hitems := congrArg (fun q : F.Observation => q.2.1) heq
    rw [h.advancePerm_apply o] at hitems
    exact (h.itemMate_item (h.setMate o)).symm.trans hitems

/-- Choose one of each pair of advance factors as positive. -/
noncomputable def factorSign (h : F.Eulerian)
    (c : h.advancePerm.cycleFactorsFinset) : ℝ := by
  letI : LinearOrder h.advancePerm.cycleFactorsFinset :=
    (Fintype.equivFin h.advancePerm.cycleFactorsFinset).linearOrder
  exact if c < h.factorMate c then 1 else -1

/-- Reflection across a choice-set pairing reverses the chosen orbit sign. -/
theorem factorSign_factorMate (h : F.Eulerian)
    (c : h.advancePerm.cycleFactorsFinset) :
    h.factorSign (h.factorMate c) = -h.factorSign c := by
  classical
  letI : LinearOrder h.advancePerm.cycleFactorsFinset :=
    (Fintype.equivFin h.advancePerm.cycleFactorsFinset).linearOrder
  unfold factorSign
  rw [h.factorMate_apply_apply]
  by_cases hlt : c < h.factorMate c
  · have hnot : ¬ h.factorMate c < c := not_lt_of_ge (le_of_lt hlt)
    simp [hlt, hnot]
  · have hrev : h.factorMate c < c :=
      (lt_or_gt_of_ne (h.factorMate_ne c)).resolve_right hlt
    simp [hlt, hrev]

/-- The advance-cycle factor containing an observation. -/
noncomputable def advanceFactor (h : F.Eulerian) (o : F.Observation) :
    h.advancePerm.cycleFactorsFinset := by
  refine ⟨h.advancePerm.cycleOf o, ?_⟩
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.mem_support]
  exact h.advancePerm_ne o

/-- A choice-set pairing moves an observation to the reflected advance factor. -/
theorem advanceFactor_setMate (h : F.Eulerian) (o : F.Observation) :
    h.advanceFactor (h.setMate o) = h.factorMate (h.advanceFactor o) := by
  have ho : o ∈ h.advancePerm.support :=
    Equiv.Perm.mem_support.mpr (h.advancePerm_ne o)
  have hmem : h.setPerm o ∈
      (h.factorMate (h.advanceFactor o) : Equiv.Perm F.Observation).support :=
    h.setPerm_mem_factorMate_support (h.advanceFactor o) o (by
      simpa [advanceFactor] using ho)
  apply Subtype.ext
  symm
  exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff h.advancePerm
    (h.factorMate (h.advanceFactor o))
    (h.factorMate (h.advanceFactor o)).2 (h.setMate o)).mpr hmem

/-- Advancing once leaves the containing advance factor unchanged. -/
theorem advanceFactor_advance (h : F.Eulerian) (o : F.Observation) :
    h.advanceFactor (h.advancePerm o) = h.advanceFactor o := by
  apply Subtype.ext
  simp [advanceFactor]

/-- The item-side pairing has the same reflected factor as the choice-set
pairing, because it is one advance step after that pairing. -/
theorem advanceFactor_itemMate (h : F.Eulerian) (o : F.Observation) :
    h.advanceFactor (h.itemMate o) = h.factorMate (h.advanceFactor o) := by
  have hstep : h.advancePerm (h.setMate o) = h.itemMate o := by
    rw [h.advancePerm_apply]
    rw [h.setMate_apply_apply]
  calc
    h.advanceFactor (h.itemMate o) = h.advanceFactor (h.advancePerm (h.setMate o)) := by
      rw [hstep]
    _ = h.advanceFactor (h.setMate o) := h.advanceFactor_advance (h.setMate o)
    _ = h.factorMate (h.advanceFactor o) := h.advanceFactor_setMate o

end Eulerian

end ChoiceFrame

end SeshadriUgander2020IIATesting
