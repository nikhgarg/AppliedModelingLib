import GN21DriverSurgePricing.ProofInterface

/-!
# Post-paper audit: Driver Surge Pricing

This ledger gives source-numbered entrypoints for the current v11
source-facing interface.  Each entry names one source claim and its paired
Lean proof endpoint; the semantic statement itself is defined only once in
`PaperInterface.lean`.
-/

namespace GN21DriverSurgePricing
namespace PostPaperAudit

/-! ## Source-model definitions -/

abbrev audit_definition_incentive_compatibility :=
  @PaperInterface.review_definition_incentive_compatible_realizes_spec
abbrev audit_definition_surge_state :=
  @PaperInterface.review_definition_surge_state_realizes_spec

/-! ## Main-text results -/

abbrev audit_theorem1_single_state_threshold_best_response :=
  @PaperInterface.review_theorem1_single_state_threshold_best_response
abbrev audit_proposition3_1_affine_single_state_ic :=
  @PaperInterface.review_proposition3_1_affine_single_state_ic
abbrev audit_theorem2_multiplicative_policy_shape :=
  @PaperInterface.review_theorem2_multiplicative_policy_shape_source_claim
abbrev audit_theorem2_positive_finite_cutoff_not_ic :=
  @PaperInterface.review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states
abbrev audit_lemma1_dynamic_reward_decomposition :=
  @PaperInterface.review_lemma1_measured_dynamic_reward_decomposition
abbrev audit_lemma1_dynamic_reward_decomposition_actual_calendar :=
  @PaperInterface.review_lemma1_measured_dynamic_reward_decomposition_of_actual_calendar
abbrev audit_lemma2_switch_probability_formula :=
  @PaperInterface.review_lemma2_switch_probability_formula
abbrev audit_lemma3_time_fraction_formula :=
  @PaperInterface.review_lemma3_measured_time_fraction_formula
abbrev audit_lemma3_time_fraction_formula_actual_calendar :=
  @PaperInterface.review_lemma3_measured_time_fraction_formula_of_actual_calendar
abbrev audit_theorem3_structured_pricing :=
  @PaperInterface.review_theorem3_structured_pricing

/-! ## Appendix results -/

abbrev audit_lemma4_threshold_uniqueness :=
  @PaperInterface.review_lemma4_single_state_threshold_uniqueness
abbrev audit_lemma5_variational_policy_forms :=
  @PaperInterface.lemma5_full_variational_policy_forms
abbrev audit_lemma6_endpoint_derivative_formula :=
  @PaperInterface.review_lemma6_upper_endpoint_derivative_formula
abbrev audit_lemma7_positive_additive_quasi_convexity :=
  @PaperInterface.review_lemma7_affine_positive_additive_response_quasi_convex
abbrev audit_lemma8_negative_additive_quasi_concavity :=
  @PaperInterface.review_lemma8_affine_negative_additive_response_quasi_concave
abbrev audit_lemma9_surge_derivative_positivity :=
  @PaperInterface.review_lemma9_surge_derivative_positive_of_acceptAll_bounds
abbrev audit_lemma10_nonsurge_derivative_positivity :=
  @PaperInterface.review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds
abbrev audit_theorem4_structural_policy_forms :=
  @PaperInterface.review_theorem4_full_structural_policy_forms_direct

end PostPaperAudit
end GN21DriverSurgePricing
