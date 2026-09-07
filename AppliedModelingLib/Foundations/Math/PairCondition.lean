import Mathlib.Data.Real.Basic

namespace AppliedModelingLib

/-!
# Two-Element Condition Helpers

Reusable logic for source proofs that case-split over two named alternatives.

## Main declarations

- `ExactlyOneOfTwo`
- `exactlyOneOfTwo_congr`
- `exactlyOneOfTwo_qualified_cutoff_iff_of_case_analysis`
- `exactlyOneOfTwo_iff_existsUnique_mem_pair`
-/

/-- Exactly one of two named elements satisfies `condition`. -/
def ExactlyOneOfTwo {α : Type*} (a b : α) (condition : α → Prop) : Prop :=
  (condition a ∧ ¬ condition b) ∨ (condition b ∧ ¬ condition a)

/-- Congruence for `ExactlyOneOfTwo` under pointwise condition equivalence at the two elements. -/
theorem exactlyOneOfTwo_congr
    {α : Type*} {a b : α} {condition condition' : α → Prop}
    (ha : condition a ↔ condition' a)
    (hb : condition b ↔ condition' b) :
    ExactlyOneOfTwo a b condition ↔
      ExactlyOneOfTwo a b condition' := by
  constructor
  · intro h
    rcases h with ⟨ha_true, hb_false⟩ | ⟨hb_true, ha_false⟩
    · exact Or.inl ⟨ha.mp ha_true, fun hb' => hb_false (hb.mpr hb')⟩
    · exact Or.inr ⟨hb.mp hb_true, fun ha' => ha_false (ha.mpr ha')⟩
  · intro h
    rcases h with ⟨ha_true, hb_false⟩ | ⟨hb_true, ha_false⟩
    · exact Or.inl ⟨ha.mpr ha_true, fun hb0 => hb_false (hb.mp hb0)⟩
    · exact Or.inr ⟨hb.mpr hb_true, fun ha0 => ha_false (ha.mp ha0)⟩

/--
Two-case branch analysis: a deviation is profitable exactly when exactly one
of two elements satisfies both a qualifier and the relevant cutoff case.
-/
theorem exactlyOneOfTwo_qualified_cutoff_iff_of_case_analysis
    {α : Type*} {a b : α}
    {qualifier cutoffCase : α → Prop}
    {deviationProfitable : Prop}
    (hnone :
      ¬ cutoffCase a → ¬ cutoffCase b → ¬ deviationProfitable)
    (hboth_impossible :
      cutoffCase a → cutoffCase b → False)
    (honlyA :
      cutoffCase a → ¬ cutoffCase b →
        (deviationProfitable ↔ qualifier a))
    (honlyB :
      cutoffCase b → ¬ cutoffCase a →
        (deviationProfitable ↔ qualifier b)) :
    deviationProfitable ↔
      ExactlyOneOfTwo a b (fun g => qualifier g ∧ cutoffCase g) := by
  by_cases hAcut : cutoffCase a
  · by_cases hBcut : cutoffCase b
    · exact False.elim (hboth_impossible hAcut hBcut)
    · have hdev_iff : deviationProfitable ↔ qualifier a :=
        honlyA hAcut hBcut
      constructor
      · intro hdev
        exact Or.inl ⟨⟨hdev_iff.mp hdev, hAcut⟩,
          fun hBqualified => hBcut hBqualified.2⟩
      · intro hexact
        rcases hexact with ⟨hAqualified, _hnotB⟩ | ⟨hBqualified, _hnotA⟩
        · exact hdev_iff.mpr hAqualified.1
        · exact False.elim (hBcut hBqualified.2)
  · by_cases hBcut : cutoffCase b
    · have hdev_iff : deviationProfitable ↔ qualifier b :=
        honlyB hBcut hAcut
      constructor
      · intro hdev
        exact Or.inr ⟨⟨hdev_iff.mp hdev, hBcut⟩,
          fun hAqualified => hAcut hAqualified.2⟩
      · intro hexact
        rcases hexact with ⟨hAqualified, _hnotB⟩ | ⟨hBqualified, _hnotA⟩
        · exact False.elim (hAcut hAqualified.2)
        · exact hdev_iff.mpr hBqualified.1
    · constructor
      · intro hdev
        exact False.elim (hnone hAcut hBcut hdev)
      · intro hexact
        rcases hexact with ⟨hAqualified, _hnotB⟩ | ⟨hBqualified, _hnotA⟩
        · exact False.elim (hAcut hAqualified.2)
        · exact False.elim (hBcut hBqualified.2)

/--
`ExactlyOneOfTwo` is equivalent to uniqueness over the two-element set named by
`a` and `b`.
-/
theorem exactlyOneOfTwo_iff_existsUnique_mem_pair
    {α : Type*} {a b : α} (hne : a ≠ b) (condition : α → Prop) :
    ExactlyOneOfTwo a b condition ↔
      ∃ g : α,
        (g = a ∨ g = b) ∧ condition g ∧
          ∀ h : α, (h = a ∨ h = b) → condition h → h = g := by
  constructor
  · intro hone
    rcases hone with ⟨ha, hnb⟩ | ⟨hb, hna⟩
    · refine ⟨a, Or.inl rfl, ha, ?_⟩
      intro h hmem hh
      rcases hmem with rfl | rfl
      · rfl
      · exact False.elim (hnb hh)
    · refine ⟨b, Or.inr rfl, hb, ?_⟩
      intro h hmem hh
      rcases hmem with rfl | rfl
      · exact False.elim (hna hh)
      · rfl
  · rintro ⟨g, hmem, hg, hunique⟩
    rcases hmem with hga | hgb
    · refine Or.inl ⟨?_, ?_⟩
      · simpa [hga] using hg
      intro hb
      have hb_eq_g : b = g := hunique b (Or.inr rfl) hb
      have hb_eq_a : b = a := hb_eq_g.trans hga
      exact hne hb_eq_a.symm
    · refine Or.inr ⟨?_, ?_⟩
      · simpa [hgb] using hg
      intro ha
      have ha_eq_g : a = g := hunique a (Or.inl rfl) ha
      have ha_eq_b : a = b := ha_eq_g.trans hgb
      exact hne ha_eq_b

end AppliedModelingLib
