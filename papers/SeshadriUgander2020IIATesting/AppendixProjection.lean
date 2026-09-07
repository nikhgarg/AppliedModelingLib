import SeshadriUgander2020IIATesting.ChoiceSystem
import SeshadriUgander2020IIATesting.AppendixEntropy

/-!
# IIA projection invariance

Source: Seshadri--Ugander (2020), Appendix, Lemma `iia_invariance`.

The proof reduces the IIA log likelihood to set and item sufficient
statistics.  This file first formalizes the finite reindexing algebra; the
source-facing I-projection theorem is added below it.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- Swap the two descriptions of an incidence: first by choice set and then
item, or first by item and then choice set. -/
noncomputable def observationSwapEquiv (F : ChoiceFrame) :
    F.Observation ≃ Sigma fun x : F.Item => {C : F.SetId // x ∈ F.members C} where
  toFun o := ⟨o.2.1, ⟨o.1, o.2.2⟩⟩
  invFun o := ⟨o.2.1, ⟨o.1, o.2.2⟩⟩
  left_inv := by rintro ⟨C, x⟩; rfl
  right_inv := by rintro ⟨x, C⟩; rfl

/-- Integrating a score of the form `a C + b x` against a choice system
depends only on its set and item marginals. -/
theorem sum_mass_mul_set_add_item (q : ChoiceSystem F)
    (a : F.SetId → ℝ) (b : F.Item → ℝ) :
    (∑ o : F.Observation, q.mass o * (a o.1 + b o.2.1)) =
      (∑ C : F.SetId, q.setMass C * a C) +
        ∑ x : F.Item, q.itemMass x * b x := by
  classical
  calc
    (∑ o : F.Observation, q.mass o * (a o.1 + b o.2.1)) =
        ∑ C : F.SetId, ∑ x : {x : F.Item // x ∈ F.members C},
          q.mass ⟨C, x⟩ * (a C + b x.1) := by
            change (∑ o : Sigma fun C : F.SetId => {x : F.Item // x ∈ F.members C},
              q.mass o * (a o.1 + b o.2.1)) = _
            rw [Fintype.sum_sigma]
    _ = ∑ C : F.SetId, ∑ x : {x : F.Item // x ∈ F.members C},
          (q.mass ⟨C, x⟩ * a C + q.mass ⟨C, x⟩ * b x.1) := by
            apply Finset.sum_congr rfl
            intro C _
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ =
        (∑ C : F.SetId, ∑ x : {x : F.Item // x ∈ F.members C},
          q.mass ⟨C, x⟩ * a C) +
        ∑ C : F.SetId, ∑ x : {x : F.Item // x ∈ F.members C},
          q.mass ⟨C, x⟩ * b x.1 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro C _
            rw [Finset.sum_add_distrib]
    _ =
        (∑ C : F.SetId, q.setMass C * a C) +
        ∑ C : F.SetId, ∑ x : {x : F.Item // x ∈ F.members C},
          q.mass ⟨C, x⟩ * b x.1 := by
            congr 1
            apply Finset.sum_congr rfl
            intro C _
            rw [← Finset.sum_mul]
            rfl
    _ =
        (∑ C : F.SetId, q.setMass C * a C) +
        ∑ x : F.Item, ∑ C : {C : F.SetId // x ∈ F.members C},
          q.mass ⟨C.1, ⟨x, C.2⟩⟩ * b x := by
            congr 1
            calc
              (∑ C : F.SetId, ∑ x : {x : F.Item // x ∈ F.members C},
                q.mass ⟨C, x⟩ * b x.1) =
                  ∑ o : F.Observation, q.mass o * b o.2.1 := by
                    change _ = ∑ o : Sigma fun C : F.SetId =>
                      {x : F.Item // x ∈ F.members C}, q.mass o * b o.2.1
                    rw [Fintype.sum_sigma]
              _ = ∑ xC : Sigma fun x : F.Item => {C : F.SetId // x ∈ F.members C},
                  q.mass ⟨xC.2.1, ⟨xC.1, xC.2.2⟩⟩ * b xC.1 := by
                    refine Fintype.sum_equiv (observationSwapEquiv F)
                      (fun o => q.mass o * b o.2.1)
                      (fun xC => q.mass ⟨xC.2.1, ⟨xC.1, xC.2.2⟩⟩ * b xC.1) ?_
                    intro o
                    rfl
              _ = ∑ x : F.Item, ∑ C : {C : F.SetId // x ∈ F.members C},
                  q.mass ⟨C.1, ⟨x, C.2⟩⟩ * b x := by
                    rw [Fintype.sum_sigma]
    _ = (∑ C : F.SetId, q.setMass C * a C) +
        ∑ x : F.Item, q.itemMass x * b x := by
            congr 1
            apply Finset.sum_congr rfl
            intro x _
            rw [← Finset.sum_mul]
            rfl

/-- Equal set and item marginals give equal expectations for every separable
incidence score. -/
theorem sum_mass_mul_set_add_item_eq_of_marginals
    (q₁ q₂ : ChoiceSystem F) (a : F.SetId → ℝ) (b : F.Item → ℝ)
    (hset : ∀ C, q₁.setMass C = q₂.setMass C)
    (hitem : ∀ x, q₁.itemMass x = q₂.itemMass x) :
    (∑ o : F.Observation, q₁.mass o * (a o.1 + b o.2.1)) =
      ∑ o : F.Observation, q₂.mass o * (a o.1 + b o.2.1) := by
  rw [sum_mass_mul_set_add_item, sum_mass_mul_set_add_item]
  simp_rw [hset, hitem]

/-- The real cross-entropy objective of two finite choice systems. -/
noncomputable def crossEntropy (q p : ChoiceSystem F) : ℝ :=
  -∑ o : F.Observation, q.mass o * Real.log (p.mass o)

/-- The finite-real KL expression used for the IIA projection objective. -/
noncomputable def klDivergence (q p : ChoiceSystem F) : ℝ :=
  ∑ o : F.Observation, q.mass o * (Real.log (q.mass o) - Real.log (p.mass o))

/-- A choice system is in the source's IIA model with positive sampling mass
on every observed choice set. -/
noncomputable def IIAInterior (p : ChoiceSystem F) : Prop :=
  p.SatisfiesIIA ∧ p.PositiveSetMass

/-- Set-specific part of the logarithm of an interior IIA choice-system mass. -/
noncomputable def iiaSetLogPotential (p : ChoiceSystem F) (γ : F.Item → ℝ)
    (C : F.SetId) : ℝ :=
  Real.log (p.setMass C) - Real.log (∑ z ∈ F.members C, γ z)

/-- Item-specific part of the logarithm of an IIA choice-system mass. -/
noncomputable def iiaItemLogPotential (γ : F.Item → ℝ) (x : F.Item) : ℝ :=
  Real.log (γ x)

/-- The IIA mass factorization makes its log mass a sum of a choice-set
potential and an item potential. -/
theorem log_mass_eq_iiaSet_add_iiaItem
    (p : ChoiceSystem F) (γ : F.Item → ℝ)
    (hγ : ∀ x, 0 < γ x)
    (hmass : ∀ C x, p.mass ⟨C, x⟩ =
      p.setMass C * γ x.1 / ∑ z ∈ F.members C, γ z)
    (hset : p.PositiveSetMass) (C : F.SetId)
    (x : {x : F.Item // x ∈ F.members C}) :
    Real.log (p.mass ⟨C, x⟩) =
      iiaSetLogPotential p γ C + iiaItemLogPotential γ x.1 := by
  have hmembers : (F.members C).Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le (by omega) (F.card_two_le C)
  obtain ⟨z, hz⟩ := hmembers
  have hden_pos : 0 < ∑ z ∈ F.members C, γ z := by
    refine Finset.sum_pos' (fun y hy => (hγ y).le) ?_
    exact ⟨z, hz, hγ z⟩
  have hnum_pos : 0 < p.setMass C * γ x.1 :=
    mul_pos (hset C) (hγ x.1)
  rw [hmass C x, Real.log_div hnum_pos.ne' hden_pos.ne',
    Real.log_mul (hset C).ne' (hγ x.1).ne']
  unfold iiaSetLogPotential iiaItemLogPotential
  ring

/-- IIA cross entropy depends on a data choice system only through its set
and item marginals. -/
theorem crossEntropy_eq_of_marginals_iia
    (q₁ q₂ p : ChoiceSystem F)
    (hset : ∀ C, q₁.setMass C = q₂.setMass C)
    (hitem : ∀ x, q₁.itemMass x = q₂.itemMass x)
    (hpIIA : p.SatisfiesIIA) (hpSet : p.PositiveSetMass) :
    crossEntropy q₁ p = crossEntropy q₂ p := by
  rcases hpIIA with ⟨γ, hγ, hmass⟩
  have hlog : ∀ o : F.Observation,
      Real.log (p.mass o) =
        iiaSetLogPotential p γ o.1 + iiaItemLogPotential γ o.2.1 := by
    rintro ⟨C, x⟩
    exact log_mass_eq_iiaSet_add_iiaItem p γ hγ hmass hpSet C x
  unfold crossEntropy
  simp_rw [hlog]
  rw [sum_mass_mul_set_add_item_eq_of_marginals q₁ q₂
    (iiaSetLogPotential p γ) (iiaItemLogPotential γ) hset hitem]

/-- KL is the data-only negative-entropy term plus cross entropy. -/
theorem klDivergence_eq_dataTerm_add_crossEntropy (q p : ChoiceSystem F) :
    klDivergence q p =
      (∑ o : F.Observation, q.mass o * Real.log (q.mass o)) + crossEntropy q p := by
  unfold klDivergence crossEntropy
  calc
    (∑ o : F.Observation,
        q.mass o * (Real.log (q.mass o) - Real.log (p.mass o))) =
        ∑ o : F.Observation,
          (q.mass o * Real.log (q.mass o) - q.mass o * Real.log (p.mass o)) := by
            apply Finset.sum_congr rfl
            intro o _
            ring
    _ = (∑ o : F.Observation, q.mass o * Real.log (q.mass o)) -
          ∑ o : F.Observation, q.mass o * Real.log (p.mass o) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ o : F.Observation, q.mass o * Real.log (q.mass o)) +
          -(∑ o : F.Observation, q.mass o * Real.log (p.mass o)) := by ring

/-- Argmin set for the IIA projection in the source's positive-set-mass
model. -/
noncomputable def iiaProjection (q : ChoiceSystem F) : Set (ChoiceSystem F) :=
  {p | p.IIAInterior ∧ ∀ r, r.IIAInterior → klDivergence q p ≤ klDivergence q r}

/-- Appendix Lemma `iia_invariance`: two choice systems with the same set
and item marginals have exactly the same KL projections onto the positive IIA
model. -/
theorem iiaProjection_eq_of_marginals
    (q₁ q₂ : ChoiceSystem F)
    (hset : ∀ C, q₁.setMass C = q₂.setMass C)
    (hitem : ∀ x, q₁.itemMass x = q₂.itemMass x) :
    iiaProjection q₁ = iiaProjection q₂ := by
  ext p
  constructor
  · rintro ⟨hp, hpmin⟩
    refine ⟨hp, ?_⟩
    intro r hr
    have hmin := hpmin r hr
    have hcep := crossEntropy_eq_of_marginals_iia q₁ q₂ p hset hitem hp.1 hp.2
    have hcer := crossEntropy_eq_of_marginals_iia q₁ q₂ r hset hitem hr.1 hr.2
    rw [klDivergence_eq_dataTerm_add_crossEntropy,
      klDivergence_eq_dataTerm_add_crossEntropy] at hmin
    rw [hcep, hcer] at hmin
    rw [klDivergence_eq_dataTerm_add_crossEntropy,
      klDivergence_eq_dataTerm_add_crossEntropy]
    linarith
  · rintro ⟨hp, hpmin⟩
    refine ⟨hp, ?_⟩
    intro r hr
    have hmin := hpmin r hr
    have hcep := crossEntropy_eq_of_marginals_iia q₂ q₁ p
      (fun C => (hset C).symm) (fun x => (hitem x).symm) hp.1 hp.2
    have hcer := crossEntropy_eq_of_marginals_iia q₂ q₁ r
      (fun C => (hset C).symm) (fun x => (hitem x).symm) hr.1 hr.2
    rw [klDivergence_eq_dataTerm_add_crossEntropy,
      klDivergence_eq_dataTerm_add_crossEntropy] at hmin
    rw [hcep, hcer] at hmin
    rw [klDivergence_eq_dataTerm_add_crossEntropy,
      klDivergence_eq_dataTerm_add_crossEntropy]
    linarith

end ChoiceSystem

end SeshadriUgander2020IIATesting
