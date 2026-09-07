import PKG25NoFreeLunch.PaperInterface

/-!
# Proof-facing interface: A No Free Lunch Theorem for Human-AI Collaboration

Each declaration in this file is the distinct Lean-checked endpoint for one
asserted source result.  Source definitions, formulas, models, and conventions
are reviewed through their actual declarations rather than theorem-shaped
wrappers.
-/

namespace PKG25NoFreeLunch

/-- Checked endpoint for the main no-free-lunch theorem. -/
theorem source_theorem1_no_free_lunch_provesSpec
    {n : ℕ} [Nonempty (Fin n)] (C : SourceCollaborationStrategy n) :
    source_theorem1_no_free_lunchSpec C := by
  unfold source_theorem1_no_free_lunchSpec
  exact source_theorem1_no_free_lunch_source C

/-- Checked endpoint for Proposition 6. -/
theorem source_proposition6_linear_combination_provesSpec :
    source_proposition6_linear_combinationSpec := by
  unfold source_proposition6_linear_combinationSpec
  exact source_proposition6_linear_combination_source_settings

/-- The printed unnumbered reverse implication is refuted by a boundary strategy. -/
theorem source_unnumbered_iff_restatement_refutesSpec :
    ¬ source_unnumbered_iff_restatementSpec := by
  intro hiff
  have hboundary := source_iff_converse_boundary_counterexample
  exact hboundary.2 ((hiff boundaryFlipStrategy).mpr hboundary.1)

/-- Checked endpoint for Proposition 7. -/
theorem source_proposition7_fixed_deferral_provesSpec :
    source_proposition7_fixed_deferralSpec := by
  intro n inst C hrel
  exact source_proposition7_reliability_forces_fixed_deferral_source C hrel

/-- Checked endpoint for Lemma 8. -/
theorem source_lemma8_bad_tuple_provesSpec :
    source_lemma8_bad_tupleSpec := by
  intro n C p hp k hhalf hbad
  exact source_lemma8_bad_tuple_source_counterexample_setting hp hhalf hbad

/-- Checked endpoint for Proposition 9. -/
theorem source_proposition9_constant_tie_label_provesSpec :
    source_proposition9_constant_tie_labelSpec := by
  intro n inst C k hrel hk
  exact source_proposition9_reliability_forces_fixed_tie_label_source C k hrel hk

end PKG25NoFreeLunch
