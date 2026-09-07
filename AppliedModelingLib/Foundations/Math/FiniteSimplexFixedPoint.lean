import AppliedModelingLib.Foundations.Math.FixedPoint.Brouwer

/-!
# Brouwer fixed points on arbitrary finite simplices

The underlying Scarf--Brouwer proof is indexed by `Fin n`.  This module
transports it along `Fintype.equivFin`, yielding the reusable form needed by
finite probability models indexed by an arbitrary nonempty finite type.

## Main declarations

- `exists_fixedPoint_finiteSimplex`
-/

namespace AppliedModelingLib

/-- Every continuous self-map of a nonempty finite real simplex has a fixed point. -/
theorem exists_fixedPoint_finiteSimplex
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
    (responseMap : stdSimplex ℝ Outcome → stdSimplex ℝ Outcome)
    (hcontinuous : Continuous responseMap) :
    ∃ policyMass : stdSimplex ℝ Outcome, responseMap policyMass = policyMass := by
  classical
  let dimension : ℕ+ := ⟨Fintype.card Outcome, Fintype.card_pos⟩
  let reindex : Outcome ≃ Fin dimension := Fintype.equivFin Outcome
  let toFin : stdSimplex ℝ Outcome → stdSimplex ℝ (Fin dimension) :=
    stdSimplex.map reindex
  let fromFin : stdSimplex ℝ (Fin dimension) → stdSimplex ℝ Outcome :=
    stdSimplex.map reindex.symm
  have hfrom_to : ∀ policyMass : stdSimplex ℝ Outcome,
      fromFin (toFin policyMass) = policyMass := by
    intro policyMass
    unfold fromFin toFin
    rw [stdSimplex.map_comp_apply]
    have hreindex : reindex.symm ∘ reindex = id := by
      funext response
      simp
    rw [hreindex, stdSimplex.map_id_apply]
  have hcontinuous_toFin : Continuous toFin := stdSimplex.continuous_map reindex
  have hcontinuous_fromFin : Continuous fromFin := stdSimplex.continuous_map reindex.symm
  let reindexedResponseMap :
      stdSimplex ℝ (Fin dimension) → stdSimplex ℝ (Fin dimension) :=
    toFin ∘ responseMap ∘ fromFin
  have hcontinuous_reindexed : Continuous reindexedResponseMap :=
    hcontinuous_toFin.comp (hcontinuous.comp hcontinuous_fromFin)
  obtain ⟨policyMass, hfixed⟩ := Brouwer reindexedResponseMap hcontinuous_reindexed
  refine ⟨fromFin policyMass, ?_⟩
  have htransported := congrArg fromFin hfixed
  calc
    responseMap (fromFin policyMass) =
        fromFin (toFin (responseMap (fromFin policyMass))) :=
      (hfrom_to (responseMap (fromFin policyMass))).symm
    _ = fromFin (reindexedResponseMap policyMass) := by rfl
    _ = fromFin policyMass := htransported

end AppliedModelingLib
