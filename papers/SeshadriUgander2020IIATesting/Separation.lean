import SeshadriUgander2020IIATesting.CycleAlgebra

/-!
# Relaxing distance to IIA

Source: the proof of Lemma 2, equation (6).  The manuscript relaxes the IIA
distance problem by dropping simplex normalizations and absorbing a
choice-set-specific normalizer into a nonnegative weight `w_C`.  This file
checks that every genuine IIA system induces one such feasible relaxed point;
therefore a lower bound for the relaxed objective is also a lower bound for
distance to IIA.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace ChoiceSystem

variable {F : ChoiceFrame}

/-- The unnormalized rank-one objective in source equation (6), including the
source's factor `1/2`. -/
noncomputable def relaxedIIAObjective (q : ChoiceSystem F) (w : F.SetId → ℝ)
    (γ : F.Item → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ o : F.Observation, |q.mass o - w o.1 * γ o.2.1|

/-- The source alternative class `𝓜_{δ,𝒞}`, written without an infimum: every
IIA choice system is at total-variation distance at least `δ`. -/
def SeparatedFromIIA (q : ChoiceSystem F) (δ : ℝ) : Prop :=
  ∀ p : ChoiceSystem F, SatisfiesIIA p → δ ≤ totalVariation q p

/-- Choice-set normalization absorbed into the relaxed weight in source
equation (6). -/
noncomputable def relaxedWeight (p : ChoiceSystem F) (γ : F.Item → ℝ)
    (C : F.SetId) : ℝ :=
  p.setMass C / ∑ z ∈ F.members C, γ z

theorem sum_scores_pos (γ : F.Item → ℝ) (hγ_pos : ∀ x, 0 < γ x)
    (C : F.SetId) : 0 < ∑ z ∈ F.members C, γ z := by
  apply Finset.sum_pos
  · intro z hz
    exact hγ_pos z
  · apply Finset.card_pos.mp
    exact lt_of_lt_of_le (by omega) (F.card_two_le C)

theorem relaxedWeight_nonneg (p : ChoiceSystem F) (γ : F.Item → ℝ)
    (hγ_pos : ∀ x, 0 < γ x) (C : F.SetId) : 0 ≤ relaxedWeight p γ C := by
  exact div_nonneg (p.setMass_nonneg C) (sum_scores_pos γ hγ_pos C).le

/-- A source IIA representation is an exact feasible point of the relaxation.
The displayed equality is the formal version of absorbing the denominator in
the proof of source equation (6). -/
theorem iia_mass_eq_relaxed_rank_one (p : ChoiceSystem F) (γ : F.Item → ℝ)
    (hγ_pos : ∀ x, 0 < γ x)
    (hrepresentation : ∀ C x, p.mass ⟨C, x⟩ =
      p.setMass C * γ x.1 / ∑ z ∈ F.members C, γ z) (C : F.SetId)
    (x : {x : F.Item // x ∈ F.members C}) :
    p.mass ⟨C, x⟩ = relaxedWeight p γ C * γ x.1 := by
  rw [hrepresentation]
  simp only [relaxedWeight]
  ring

/-- Every true IIA choice system has a feasible point in the relaxed
optimization problem with exactly its total-variation objective value. -/
theorem iia_relaxed_objective_eq_totalVariation (q p : ChoiceSystem F)
    (hp_iia : SatisfiesIIA p) :
    ∃ w : F.SetId → ℝ, ∃ γ : F.Item → ℝ,
      (∀ C, 0 ≤ w C) ∧ (∀ x, 0 < γ x) ∧
      relaxedIIAObjective q w γ = totalVariation q p := by
  obtain ⟨γ, hγ_pos, hrepresentation⟩ := hp_iia
  refine ⟨relaxedWeight p γ, γ, ?_, hγ_pos, ?_⟩
  · intro C
    exact relaxedWeight_nonneg p γ hγ_pos C
  · unfold relaxedIIAObjective totalVariation
    congr 2
    apply funext
    rintro ⟨C, x⟩
    rw [iia_mass_eq_relaxed_rank_one p γ hγ_pos hrepresentation]

/-- Any lower bound valid for every feasible relaxed rank-one objective is a
valid lower bound on distance from the IIA family. This is the formal
relaxation direction used in the proof of source Lemma 2. -/
theorem separatedFromIIA_of_relaxed_lower_bound (q : ChoiceSystem F) (δ : ℝ)
    (hrelaxed : ∀ w γ, (∀ C, 0 ≤ w C) → (∀ x, 0 < γ x) →
      δ ≤ relaxedIIAObjective q w γ) :
    SeparatedFromIIA q δ := by
  intro p hp_iia
  obtain ⟨w, γ, hw_nonneg, hγ_pos, hobjective⟩ :=
    iia_relaxed_objective_eq_totalVariation q p hp_iia
  rw [← hobjective]
  exact hrelaxed w γ hw_nonneg hγ_pos

end ChoiceSystem

end SeshadriUgander2020IIATesting
