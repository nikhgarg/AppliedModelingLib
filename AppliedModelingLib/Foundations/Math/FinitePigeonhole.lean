import Mathlib.Tactic

/-!
# Finite fiber pigeonhole bounds
-/

namespace AppliedModelingLib

/-- Some fiber of a map between finite nonempty types has cardinality at
least the domain cardinality divided by the number of possible images, in
division-free form. -/
theorem exists_card_le_card_mul_fiberCard
    {Domain Codomain : Type*}
    [Fintype Domain] [Fintype Codomain] [DecidableEq Codomain] [Nonempty Codomain]
    (map : Domain → Codomain) :
    ∃ value : Codomain,
      Fintype.card Domain ≤ Fintype.card Codomain *
        ((Finset.univ.filter fun input : Domain ↦ map input = value).card) := by
  classical
  let fiberCard : Codomain → ℕ := fun value ↦
    (Finset.univ.filter fun input : Domain ↦ map input = value).card
  obtain ⟨largest, -, hlargest⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Codomain) fiberCard
      Finset.univ_nonempty
  refine ⟨largest, ?_⟩
  have hmaps : ((Finset.univ : Finset Domain) : Set Domain).MapsTo
      map (Finset.univ : Finset Codomain) := by
    intro input _
    simp
  have hfiberSum : Fintype.card Domain = ∑ value : Codomain, fiberCard value := by
    simpa [fiberCard] using Finset.card_eq_sum_card_fiberwise hmaps
  rw [hfiberSum]
  calc
    (∑ value : Codomain, fiberCard value) ≤ ∑ _value : Codomain, fiberCard largest := by
      apply Finset.sum_le_sum
      intro value _
      exact hlargest value (Finset.mem_univ value)
    _ = Fintype.card Codomain * fiberCard largest := by
      simp [Finset.sum_const]
    _ = Fintype.card Codomain *
        ((Finset.univ.filter fun input : Domain ↦ map input = largest).card) := by
      rfl

end AppliedModelingLib
