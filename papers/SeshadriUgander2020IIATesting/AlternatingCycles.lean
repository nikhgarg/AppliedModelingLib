import SeshadriUgander2020IIATesting.CycleDecomposition

/-!
# Alternating incidence-cycle data for Lemma 2

`CycleDecomposition` records the edge partition and its Eulerian orientation
balances, which suffice for Lemmas 3--4.  Lemma 2 additionally follows each
cycle through alternating item and choice-set vertices.  The witness below
records that concrete traversal rather than assuming a local separation
inequality.  Its derived lemmas are the bridge from the paper's informal
``waterbed'' argument to the relaxed rank-one objective.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

namespace CycleDecomposition

variable (D : CycleDecomposition F)

/-- Concrete alternating traversal data for each cycle in an explicit edge
partition. A vertex index represents a set--item incidence pair: `false` is
the edge to its current item and `true` the edge to the successor item. -/
structure AlternatingCycleWitness where
  Vertex : D.Cycle → Type
  instFintypeVertex : ∀ i, Fintype (Vertex i)
  instDecidableEqVertex : ∀ i, DecidableEq (Vertex i)
  successor : ∀ i, Equiv.Perm (Vertex i)
  setAt : ∀ i, Vertex i → F.SetId
  itemAt : ∀ i, Vertex i → F.Item
  current_mem : ∀ i v, itemAt i v ∈ F.members (setAt i v)
  successor_mem : ∀ i v, itemAt i (successor i v) ∈ F.members (setAt i v)
  edgeParamEquiv : ∀ i, Fin (D.length i) ≃ (Vertex i × Bool)
  false_edge : ∀ i v,
    D.edgeEquiv ⟨i, (edgeParamEquiv i).symm (v, false)⟩ =
      ⟨setAt i v, ⟨itemAt i v, current_mem i v⟩⟩
  true_edge : ∀ i v,
    D.edgeEquiv ⟨i, (edgeParamEquiv i).symm (v, true)⟩ =
      ⟨setAt i v, ⟨itemAt i (successor i v), successor_mem i v⟩⟩
  base_false : ∀ i v,
    D.base (D.edgeEquiv ⟨i, (edgeParamEquiv i).symm (v, false)⟩) = 1
  base_true : ∀ i v,
    D.base (D.edgeEquiv ⟨i, (edgeParamEquiv i).symm (v, true)⟩) = -1

attribute [instance] AlternatingCycleWitness.instFintypeVertex
  AlternatingCycleWitness.instDecidableEqVertex

/-- A full edge partition of the nonempty incidence support has at least one
cycle. -/
theorem cycle_nonempty : Nonempty D.Cycle := by
  obtain ⟨C⟩ := F.nonempty_sets
  obtain ⟨x, hx⟩ := Finset.card_pos.mp
    (lt_of_lt_of_le (by omega) (F.card_two_le C))
  exact ⟨(D.edgeEquiv.symm ⟨C, ⟨x, hx⟩⟩).1⟩

theorem cycle_card_pos : 0 < Fintype.card D.Cycle :=
  Fintype.card_pos_iff.mpr D.cycle_nonempty

/-- The source's average cycle length `μ(σ) = d / |σ|`. -/
noncomputable def cycleMean : ℝ :=
  (F.incidenceCount : ℝ) / (Fintype.card D.Cycle : ℝ)

theorem cycleMean_pos : 0 < D.cycleMean := by
  unfold cycleMean
  exact div_pos (by exact_mod_cast F.incidenceCount_pos)
    (by exact_mod_cast D.cycle_card_pos)

namespace AlternatingCycleWitness

variable (W : D.AlternatingCycleWitness)

theorem vertex_nonempty (i : D.Cycle) : Nonempty (W.Vertex i) := by
  let e : Fin (D.length i) := ⟨0, D.length_pos i⟩
  exact ⟨(W.edgeParamEquiv i e).1⟩

/-- The sign on a current-item edge is the cycle orientation sign. -/
theorem orientationValue_false (a : D.Cycle → Bool) (i : D.Cycle)
    (v : W.Vertex i) :
    D.orientationValue a ⟨W.setAt i v, ⟨W.itemAt i v, W.current_mem i v⟩⟩ =
      Rademacher.sign (a i) := by
  rw [← W.false_edge i v]
  simp [CycleDecomposition.orientationValue, W.base_false]

/-- The sign on a successor-item edge is the opposite cycle orientation sign. -/
theorem orientationValue_true (a : D.Cycle → Bool) (i : D.Cycle)
    (v : W.Vertex i) :
    D.orientationValue a ⟨W.setAt i v,
      ⟨W.itemAt i (W.successor i v), W.successor_mem i v⟩⟩ =
      -Rademacher.sign (a i) := by
  rw [← W.true_edge i v]
  simp [CycleDecomposition.orientationValue, W.base_true]

/-- The relaxed absolute-error contribution of one traversed cycle.  The two
targets are written in their expanded perturbation form; the next theorem
identifies them with `q_{b,ε}` using the concrete edge traversal. -/
noncomputable def localRelaxedLoss (a : D.Cycle → Bool) (ε : ℝ)
    (w : F.SetId → ℝ) (γ : F.Item → ℝ) (i : D.Cycle) : ℝ :=
  ∑ v : W.Vertex i,
    (|w (W.setAt i v) * γ (W.itemAt i v) -
      (1 + ε * Rademacher.sign (a i)) / (F.incidenceCount : ℝ)| +
    |w (W.setAt i v) * γ (W.itemAt i (W.successor i v)) -
      (1 - ε * Rademacher.sign (a i)) / (F.incidenceCount : ℝ)|)

/-- The rigorous local ``waterbed'' lower bound for either orientation of one
cycle.  It is source Lemma 2's `ε/d` absolute-loss contribution before the
outer `1/2` in total variation. -/
theorem localRelaxedLoss_lower (a : D.Cycle → Bool) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1)
    (w : F.SetId → ℝ) (γ : F.Item → ℝ)
    (hw_nonneg : ∀ C, 0 ≤ w C) (hγ_pos : ∀ x, 0 < γ x)
    (i : D.Cycle) :
    ε / (F.incidenceCount : ℝ) ≤
      localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
        (w := w) (γ := γ) (i := i) := by
  letI : Nonempty (W.Vertex i) := vertex_nonempty (D := D) (W := W) i
  have hdenom_pos : 0 < (F.incidenceCount : ℝ) := by
    exact_mod_cast F.incidenceCount_pos
  have hdenom_ne : (F.incidenceCount : ℝ) ≠ 0 := hdenom_pos.ne'
  have hcycle := CycleAlgebra.alternating_cycle_loss_lower_bound_signed
    (W.successor i) (fun v => w (W.setAt i v)) (fun v => γ (W.itemAt i v))
    (fun v => hw_nonneg (W.setAt i v))
    (fun v => (hγ_pos (W.itemAt i v)).le)
    (1 / (F.incidenceCount : ℝ)) (ε / (F.incidenceCount : ℝ))
    (Rademacher.sign (a i)) (by positivity)
    (div_nonneg hε_nonneg hdenom_pos.le)
    (Rademacher.sign_eq_one_or_neg_one (a i))
  calc
    ε / (F.incidenceCount : ℝ) ≤
        ∑ v : W.Vertex i,
          (|w (W.setAt i v) * γ (W.itemAt i v) -
              (1 / (F.incidenceCount : ℝ) +
                Rademacher.sign (a i) * (ε / (F.incidenceCount : ℝ)))| +
            |w (W.setAt i v) * γ (W.itemAt i (W.successor i v)) -
              (1 / (F.incidenceCount : ℝ) -
                Rademacher.sign (a i) * (ε / (F.incidenceCount : ℝ)))|) := hcycle
    _ = localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
        (w := w) (γ := γ) (i := i) := by
      unfold localRelaxedLoss
      apply Finset.sum_congr rfl
      intro v _
      congr 1 <;> field_simp [hdenom_ne]

/-- Reindexing a single partition cycle by its explicit alternating
traversal turns its incidence-error sum into `localRelaxedLoss`. -/
theorem sum_cycle_edge_error_eq_localRelaxedLoss (a : D.Cycle → Bool) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1)
    (w : F.SetId → ℝ) (γ : F.Item → ℝ) (i : D.Cycle) :
    (∑ e : Fin (D.length i),
      |(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass
          (D.edgeEquiv ⟨i, e⟩) -
        w (D.edgeEquiv ⟨i, e⟩).1 * γ (D.edgeEquiv ⟨i, e⟩).2.1|) =
      localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
        (w := w) (γ := γ) (i := i) := by
  calc
    (∑ e : Fin (D.length i),
      |(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass
          (D.edgeEquiv ⟨i, e⟩) -
        w (D.edgeEquiv ⟨i, e⟩).1 * γ (D.edgeEquiv ⟨i, e⟩).2.1|) =
        ∑ p : W.Vertex i × Bool,
          |(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass
              (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm p⟩) -
            w (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm p⟩).1 *
              γ (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm p⟩).2.1| := by
      refine Fintype.sum_equiv (W.edgeParamEquiv i) _ _ ?_
      intro e
      rw [(W.edgeParamEquiv i).symm_apply_apply]
    _ = ∑ v : W.Vertex i,
        (|(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass
              (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm (v, true)⟩) -
            w (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm (v, true)⟩).1 *
              γ (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm (v, true)⟩).2.1| +
          |(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass
              (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm (v, false)⟩) -
            w (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm (v, false)⟩).1 *
              γ (D.edgeEquiv ⟨i, (W.edgeParamEquiv i).symm (v, false)⟩).2.1|) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro v _
      rw [Fintype.sum_bool]
    _ = localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
        (w := w) (γ := γ) (i := i) := by
      unfold localRelaxedLoss
      apply Finset.sum_congr rfl
      intro v _
      rw [W.true_edge i v, W.false_edge i v,
        perturb_mass, perturb_mass]
      simp only [orientedSign]
      rw [
        orientationValue_true (D := D) (W := W) a i v,
        orientationValue_false (D := D) (W := W) a i v]
      rw [add_comm]
      congr 1
      · exact abs_sub_comm _ _
      · rw [abs_sub_comm]
        congr 1
        ring

/-- The relaxed objective partitions exactly into the local cycle losses. -/
theorem relaxedIIAObjective_eq_half_sum_localRelaxedLoss (a : D.Cycle → Bool)
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1)
    (w : F.SetId → ℝ) (γ : F.Item → ℝ) :
    relaxedIIAObjective (perturb (D.orientedSign a) ε hε_nonneg hε_le_one) w γ =
      (1 / 2 : ℝ) * ∑ i : D.Cycle,
        localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
          (w := w) (γ := γ) (i := i) := by
  unfold relaxedIIAObjective
  congr 1
  calc
    (∑ o : F.Observation,
      |(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass o -
        w o.1 * γ o.2.1|) =
        ∑ e : Sigma fun i => Fin (D.length i),
          |(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass
              (D.edgeEquiv e) -
            w (D.edgeEquiv e).1 * γ (D.edgeEquiv e).2.1| := by
      symm
      refine Fintype.sum_equiv D.edgeEquiv _ _ ?_
      intro e
      rfl
    _ = ∑ i : D.Cycle, ∑ e : Fin (D.length i),
          |(perturb (D.orientedSign a) ε hε_nonneg hε_le_one).mass
              (D.edgeEquiv ⟨i, e⟩) -
            w (D.edgeEquiv ⟨i, e⟩).1 * γ (D.edgeEquiv ⟨i, e⟩).2.1| := by
      rw [Fintype.sum_sigma]
    _ = ∑ i : D.Cycle,
        localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
          (w := w) (γ := γ) (i := i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_cycle_edge_error_eq_localRelaxedLoss
        (D := D) (W := W) a ε hε_nonneg hε_le_one w γ i

/-- Summing the local waterbed losses over the explicit cycle partition gives
the paper's `ε |σ| /(2d)` relaxed lower bound. -/
theorem relaxedIIAObjective_lower_from_cycles (W : D.AlternatingCycleWitness)
    (a : D.Cycle → Bool) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1)
    (w : F.SetId → ℝ) (γ : F.Item → ℝ)
    (hw_nonneg : ∀ C, 0 ≤ w C) (hγ_pos : ∀ x, 0 < γ x) :
    ε * (Fintype.card D.Cycle : ℝ) / (2 * (F.incidenceCount : ℝ)) ≤
      relaxedIIAObjective (perturb (D.orientedSign a) ε hε_nonneg hε_le_one) w γ := by
  have hlocal : (∑ i : D.Cycle, ε / (F.incidenceCount : ℝ)) ≤
      ∑ i : D.Cycle,
        localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
          (w := w) (γ := γ) (i := i) := by
    apply Finset.sum_le_sum
    intro i _
    exact localRelaxedLoss_lower (D := D) (W := W) a ε hε_nonneg hε_le_one
      w γ hw_nonneg hγ_pos i
  have hdenom : (F.incidenceCount : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt F.incidenceCount_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlocal
  have hlocal' : (ε / (F.incidenceCount : ℝ)) * (Fintype.card D.Cycle : ℝ) ≤
      ∑ i : D.Cycle,
        localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
          (w := w) (γ := γ) (i := i) := by
    simpa [mul_comm] using hlocal
  calc
    ε * (Fintype.card D.Cycle : ℝ) / (2 * (F.incidenceCount : ℝ)) =
        (1 / 2 : ℝ) *
          ((ε / (F.incidenceCount : ℝ)) * (Fintype.card D.Cycle : ℝ)) := by
      field_simp [hdenom]
    _ ≤ (1 / 2 : ℝ) * ∑ i : D.Cycle,
        localRelaxedLoss (D := D) (W := W) (a := a) (ε := ε)
          (w := w) (γ := γ) (i := i) :=
      mul_le_mul_of_nonneg_left hlocal' (by norm_num)
    _ = relaxedIIAObjective (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)
        w γ := (relaxedIIAObjective_eq_half_sum_localRelaxedLoss
          (D := D) (W := W) a ε hε_nonneg hε_le_one w γ).symm

/-- Lemma 2's separation conclusion for every independently oriented cycle
perturbation, with its exact `ε |σ| /(2d)` radius. -/
theorem orientedSign_separatedFromIIA (W : D.AlternatingCycleWitness)
    (a : D.Cycle → Bool) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    SeparatedFromIIA (perturb (D.orientedSign a) ε hε_nonneg hε_le_one)
      (ε * (Fintype.card D.Cycle : ℝ) / (2 * (F.incidenceCount : ℝ))) := by
  apply separatedFromIIA_of_relaxed_lower_bound
  intro w γ hw_nonneg hγ_pos
  exact relaxedIIAObjective_lower_from_cycles (D := D) (W := W) a ε
    hε_nonneg hε_le_one w γ hw_nonneg hγ_pos

end AlternatingCycleWitness

end CycleDecomposition

end ChoiceSystem

end SeshadriUgander2020IIATesting
