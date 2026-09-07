import SeshadriUgander2020IIATesting.CycleMixture

/-!
# Explicit cycle-decomposition witnesses

This is the combinatorial bridge for Seshadri--Ugander (2020), Lemma 4.
The source starts from an edge-disjoint decomposition of the comparison
incidence graph, fixes an alternating base orientation on each cycle, and
then independently reverses every cycle.  `CycleDecomposition` records that
finite data directly on the observation/incidence support.  Its balance
fields state the two vertex-conservation facts that are certified by an
Eulerian orientation; the following proofs derive the statistical sign
family and its exact inner-product formula.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- A finite edge-disjoint cycle decomposition of the observation incidences,
with a fixed alternating orientation on each cycle.  The equivalence makes
edge coverage and disjointness explicit. -/
structure CycleDecomposition (F : ChoiceFrame) where
  Cycle : Type
  instFintypeCycle : Fintype Cycle
  instDecidableEqCycle : DecidableEq Cycle
  length : Cycle → ℕ
  length_pos : ∀ i, 0 < length i
  edgeEquiv : (Sigma fun i => Fin (length i)) ≃ F.Observation
  base : F.Observation → ℝ
  base_eq_one_or_neg_one : ∀ o, base o = 1 ∨ base o = -1
  set_balance : ∀ a : Cycle → Bool, ∀ C,
    ∑ x : {x : F.Item // x ∈ F.members C},
      base ⟨C, x⟩ * Rademacher.sign (a (edgeEquiv.symm ⟨C, x⟩).1) = 0
  item_balance : ∀ a : Cycle → Bool, ∀ x,
    ∑ C : {C : F.SetId // x ∈ F.members C},
      base ⟨C, ⟨x, C.2⟩⟩ *
        Rademacher.sign (a (edgeEquiv.symm ⟨C, ⟨x, C.2⟩⟩).1) = 0

attribute [instance] CycleDecomposition.instFintypeCycle
  CycleDecomposition.instDecidableEqCycle

namespace CycleDecomposition

variable (D : CycleDecomposition F)

/-- The signed orientation obtained by independently choosing the direction
of every cycle. -/
noncomputable def orientationValue (a : D.Cycle → Bool) (o : F.Observation) : ℝ :=
  D.base o * Rademacher.sign (a (D.edgeEquiv.symm o).1)

theorem base_sq (o : F.Observation) : D.base o ^ 2 = 1 := by
  rcases D.base_eq_one_or_neg_one o with h | h <;> rw [h] <;> norm_num

theorem orientationValue_eq_one_or_neg_one (a : D.Cycle → Bool)
    (o : F.Observation) :
    D.orientationValue a o = 1 ∨ D.orientationValue a o = -1 := by
  rcases D.base_eq_one_or_neg_one o with hb | hb <;>
    rcases Rademacher.sign_eq_one_or_neg_one (a (D.edgeEquiv.symm o).1) with hs | hs <;>
      simp [orientationValue, hb, hs]

/-- The source perturbation associated to an orientation assignment. -/
noncomputable def orientedSign (a : D.Cycle → Bool) : BalancedSign F where
  sign := D.orientationValue a
  sign_eq_one_or_neg_one := D.orientationValue_eq_one_or_neg_one a
  set_balance := D.set_balance a
  item_balance := D.item_balance a

/-- Two oriented perturbations have exactly the cycle-weighted Rademacher
inner product used in the first line of source Lemma 4. -/
theorem signInner_orientedSign (a a' : D.Cycle → Bool) :
    signInner (D.orientedSign a) (D.orientedSign a') =
      CycleMixture.orientationInner D.length a a' := by
  classical
  unfold signInner orientedSign orientationValue CycleMixture.orientationInner
  calc
    (∑ o : F.Observation,
        (D.base o * Rademacher.sign (a (D.edgeEquiv.symm o).1)) *
          (D.base o * Rademacher.sign (a' (D.edgeEquiv.symm o).1))) =
        ∑ e : Sigma fun i => Fin (D.length i),
          (D.base (D.edgeEquiv e) * Rademacher.sign (a (D.edgeEquiv.symm (D.edgeEquiv e)).1)) *
            (D.base (D.edgeEquiv e) * Rademacher.sign
              (a' (D.edgeEquiv.symm (D.edgeEquiv e)).1)) := by
      symm
      refine Fintype.sum_equiv D.edgeEquiv _ _ ?_
      intro e
      rfl
    _ = ∑ i : D.Cycle, ∑ _e : Fin (D.length i),
          Rademacher.sign (a i) * Rademacher.sign (a' i) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro e _
      rw [D.edgeEquiv.symm_apply_apply]
      have hbase := D.base_sq (D.edgeEquiv ⟨i, e⟩)
      calc
        D.base (D.edgeEquiv ⟨i, e⟩) * Rademacher.sign (a i) *
            (D.base (D.edgeEquiv ⟨i, e⟩) * Rademacher.sign (a' i)) =
            D.base (D.edgeEquiv ⟨i, e⟩) ^ 2 *
              Rademacher.sign (a i) * Rademacher.sign (a' i) := by ring
        _ = Rademacher.sign (a i) * Rademacher.sign (a' i) := by rw [hbase]; ring
    _ = ∑ i : D.Cycle,
          (D.length i : ℝ) * Rademacher.sign (a i) * Rademacher.sign (a' i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
      ring

end CycleDecomposition

end ChoiceSystem

end SeshadriUgander2020IIATesting
