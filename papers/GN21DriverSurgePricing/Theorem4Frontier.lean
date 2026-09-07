import GN21DriverSurgePricing.MainTheorems

/-!
# Theorem 4 Frontier Routes for Driver Surge Pricing

This file exposes compact Theorem 4 endpoints that are closest to the
source proof path.  The heavy CTMC endpoint records remain in
`MainTheorems.lean`; this module packages them into reviewable paper-facing
statements.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/--
Theorem 4 endpoint for exact one-threshold source selections with explicit
accept-all escape branches.  If every non-accept-all measurable optimum has
the finite non-surge reject-long and surge reject-short endpoint data required
by the paper proof, then accept-all is the unique measurable optimum.
-/
theorem paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C :
      Theorem4MeasurableEndpointCurrentBoundsExactOneThresholdNonAcceptAllSelectionUnlessCertificate
        μ arrival m z switch12 switch21) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          ρ = acceptAllDynamicPolicy :=
    paper_theorem4_measurable_accept_all_unique_optimal_of_shape_replacement_statewise_improvements_unless
      μ arrival m z switch12 switch21
      (Theorem4MeasurableShapeReplacementStatewiseImprovementUnlessCertificate.of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
        μ arrival m z switch12 switch21 C)

/--
Theorem 4 endpoint from fixed-transfer exact one-threshold data.  The
replacement certificate supplies the Lemma 5 structural cases; the local
fixed-transfer certificate supplies the Lemma 9/10 endpoint improvements.
-/
theorem paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_theorem3_fixed_transfer_regular_exact_one_threshold_non_accept_all_selection_unless
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (Creplacement :
      Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (C :
      Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularExactOneThresholdNonAcceptAllSelectionUnlessCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          ρ = acceptAllDynamicPolicy :=
    paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
      μ arrival m z switch12 switch21
      (C.to_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
        Creplacement)

/--
Theorem 4 endpoint from the extended one-threshold aggregate-cross
fixed-transfer source package.  This is the closest compiled Theorem 4
frontier to the paper convention where an optimum may already be accept-all,
and otherwise has the finite one-threshold endpoint selected by the proof.
-/
theorem paper_theorem4_measurable_accept_all_unique_optimal_of_extended_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_source
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3ExtendedOneThresholdBranchSurgeCrossByPolicyFormFixedTransferSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          ρ = acceptAllDynamicPolicy := by
  let S :=
    D.to_exact_one_threshold_non_accept_all_selection_unless
      P hR1_pos hR1_lt_R2 hR2_pos hmeasure_surge_acceptAll_pos
  exact
    paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_theorem3_fixed_transfer_regular_exact_one_threshold_non_accept_all_selection_unless
      μ arrival m z R1 R2 switch12 switch21 S.1.to_shape_replacements S.2

/--
Theorem 4 AE endpoint from feasible a.e. Lemma 5 representatives and
positive-rejected-mass endpoint moves.  Unlike the older compatibility
wrapper, this frontier derives accept-all optimality from existence of an
optimum plus the strict rejected-mass moves, so source work does not need to
prove accept-all optimality separately.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_feasible_ae_forms_and_representative_rejected_mass_improvements_from_exists
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (forms :
      Theorem4AllMeasurableFeasibleAEPolicyFormData μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (nonsurge_reject_long_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 0) →
        0 < (μ 0) (acceptAllPolicy \ ρ 0) →
        ∀ t : ℝ,
          rejectsLongTrips t (ρ 0) →
            gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (nonsurge_accept_middle_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 0) →
        0 < (μ 0) (acceptAllPolicy \ ρ 0) →
        ∀ lo hi : ℝ,
          acceptsMiddleTrips lo hi (ρ 0) →
            gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (surge_reject_short_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 1) →
        0 < (μ 1) (acceptAllPolicy \ ρ 1) →
        ∀ t : ℝ,
          rejectsShortTrips t (ρ 1) →
            gn21SurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (surge_reject_middle_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 1) →
        0 < (μ 1) (acceptAllPolicy \ ρ 1) →
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            gn21SurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
  paper_theorem4_measurable_accept_all_ae_unique_optimal_of_measured_aggregate_feasible_rejected_mass_strict_local_improvements_from_existence_certificate
    μ arrival switch12 switch21
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
    (theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementExistenceCertificate_of_feasible_ae_forms_and_representative_rejected_mass_improvements
      μ arrival m z switch12 switch21 forms
      nonsurge_reject_long_improvement nonsurge_accept_middle_improvement
      surge_reject_short_improvement surge_reject_middle_improvement)

/--
Theorem 4 AE endpoint from fixed-response Lemma 5 policy forms and
positive-rejected-mass endpoint moves.  This is the source-facing fixed-response
version of the existence-based route above.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements_from_exists
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (forms :
      Theorem4AllMeasurableFixedResponsePolicyFormData μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (nonsurge_reject_long_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 0) →
        0 < (μ 0) (acceptAllPolicy \ ρ 0) →
        ∀ t : ℝ,
          rejectsLongTrips t (ρ 0) →
            gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (nonsurge_accept_middle_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 0) →
        0 < (μ 0) (acceptAllPolicy \ ρ 0) →
        ∀ lo hi : ℝ,
          acceptsMiddleTrips lo hi (ρ 0) →
            gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (surge_reject_short_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 1) →
        0 < (μ 1) (acceptAllPolicy \ ρ 1) →
        ∀ t : ℝ,
          rejectsShortTrips t (ρ 1) →
            gn21SurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (surge_reject_middle_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 1) →
        0 < (μ 1) (acceptAllPolicy \ ρ 1) →
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            gn21SurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
  paper_theorem4_measurable_accept_all_ae_unique_optimal_of_measured_aggregate_feasible_rejected_mass_strict_local_improvements_from_existence_certificate
    μ arrival switch12 switch21
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
    (theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementExistenceCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements
      μ arrival m z switch12 switch21 forms
      nonsurge_reject_long_improvement nonsurge_accept_middle_improvement
      surge_reject_short_improvement surge_reject_middle_improvement)

/--
Theorem 4 AE endpoint from the raw GN21 bracket fixed-response source data.
The bracket package supplies the a.e. Lemma 5 representatives; the four
positive-rejected-mass endpoint moves rule out every non-accept-all branch and
derive accept-all optimality internally.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_gn21_bracket_source_data_and_representative_rejected_mass_improvements_from_exists
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (nonsurge_reject_long_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 0) →
        0 < (μ 0) (acceptAllPolicy \ ρ 0) →
        ∀ t : ℝ,
          rejectsLongTrips t (ρ 0) →
            gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (nonsurge_accept_middle_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 0) →
        0 < (μ 0) (acceptAllPolicy \ ρ 0) →
        ∀ lo hi : ℝ,
          acceptsMiddleTrips lo hi (ρ 0) →
            gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (surge_reject_short_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 1) →
        0 < (μ 1) (acceptAllPolicy \ ρ 1) →
        ∀ t : ℝ,
          rejectsShortTrips t (ρ 1) →
            gn21SurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ)
    (surge_reject_middle_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 1) →
        0 < (μ 1) (acceptAllPolicy \ ρ 1) →
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            gn21SurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
  paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements_from_exists
    μ arrival m z switch12 switch21 forms.to_fixed_response_policy_form_data
    nonsurge_reject_long_improvement nonsurge_accept_middle_improvement
    surge_reject_short_improvement surge_reject_middle_improvement

/--
Theorem 4 AE endpoint from the by-policy-form middle-reroute fixed-transfer
source package.  This is the fixed-price version of the compiled Theorem 3
existence boundary: the local endpoint package supplies the Lemma 9/10 moves,
the replacement data supplies the Lemma 5 structural cases, and accept-all
optimality is derived from the rejected-mass strict-improvement certificate.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_middle_reroute_ae_policy_form_source_existence
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3MiddleRerouteAEPolicyFormSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_shape_replacement_statewise_rejected_mass_improvements_unless
      μ arrival m z switch12 switch21
      ((D.local_endpoint.to_shape_replacement_rejected_mass_improvements_existence_of_shape_replacements
          P hR1_pos hR1_lt_R2 hR2_pos
          hmeasure_surge_acceptAll_pos
          D.replacement.to_shape_replacements)
        |>.to_accept_all_certificate)

/--
Theorem 4 AE endpoint from the lighter common fixed-state-equality
middle-reroute source package.  This is the smallest fixed-price source package
shared with the active Theorem 3 route: equality fields are expanded to the
by-policy-form endpoint data internally, and accept-all optimality is still
derived by the rejected-mass route.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_middle_reroute_light_ae_eq_source_existence
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_middle_reroute_ae_policy_form_source_existence
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2 hR2_pos
      hmeasure_surge_acceptAll_pos
      { replacement := D.replacement
        local_endpoint := D.local_endpoint.to_by_policy_form_ae_local_endpoint }

/--
Theorem 4 AE endpoint from fixed-response policy-form data plus common
fixed-state-equality middle-reroute endpoint data.  This exposes the same
source package used by the existence-based fixed-response Theorem 3 route, but
with the fixed-price Theorem 4 conclusion.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_eq_middle_reroute_source_existence
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3FixedResponsePolicyFormEqMiddleRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  let S :=
    GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_eq_middle_reroute
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2
      hR2_pos hmeasure_surge_acceptAll_pos
      D.forms D.local_endpoint
  exact
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements_from_exists
      μ arrival m z switch12 switch21 S.forms
      S.nonsurge_reject_long_improvement
      S.nonsurge_accept_middle_improvement
      S.surge_reject_short_improvement
      S.surge_reject_middle_improvement

/--
Theorem 4 AE endpoint from one-threshold fixed-response source data plus the
common fixed-state-equality middle-reroute endpoint.  Lemma 6 supplies the
one-threshold fixed-response forms; Lean derives the rejected-mass endpoint
moves and accept-all optimality internally.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_one_threshold_eq_middle_reroute_source_existence
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3FixedResponseOneThresholdEqMiddleRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_eq_middle_reroute_source_existence
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2 hR2_pos
      hmeasure_surge_acceptAll_pos
      D.to_policy_form_source

/--
Theorem 4 AE endpoint from raw bracket-level one-threshold fixed-response
source data plus the common fixed-state-equality middle-reroute endpoint.  This
lets a source proof keep Lemma 6 at the sign-bracket layer while using the
fixed-price Theorem 4 conclusion directly.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_one_threshold_bracket_eq_middle_reroute_source_existence
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3FixedResponseOneThresholdBracketEqMiddleRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_one_threshold_eq_middle_reroute_source_existence
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2 hR2_pos
    hmeasure_surge_acceptAll_pos
    D.to_one_threshold_source

/--
Theorem 4 AE endpoint from the sharper by-policy-form middle-cutoff-reroute
endpoint boundary.  This is the fixed-price version of the current Theorem 3
frontier: source proofs supply fixed-response Lemma 5 forms and the
branch-indexed by-policy-form endpoint certificate; Lean derives the
positive-rejected-mass strict local moves.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_by_policy_form_middle_cutoff_reroute_source_existence
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3FixedResponsePolicyFormByPolicyFormMiddleCutoffRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  let S :=
    GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_by_policy_form_middle_cutoff_reroute
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2
      hR2_pos hmeasure_surge_acceptAll_pos
      D.forms D.local_endpoint
  exact
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements_from_exists
      μ arrival m z switch12 switch21 S.forms
      S.nonsurge_reject_long_improvement
      S.nonsurge_accept_middle_improvement
      S.surge_reject_short_improvement
      S.surge_reject_middle_improvement

/--
Theorem 4 AE endpoint from the aggregate fixed-surge cross-ratio
middle-cutoff-reroute boundary.  This keeps the source obligation at the
single cross-ratio comparison actually consumed by the non-surge endpoint
constructor.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_surge_cross_by_policy_form_middle_cutoff_reroute_source_existence
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3FixedResponsePolicyFormSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  let S :=
    GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData.of_fixed_state_cross_by_policy_form_middle_cutoff_reroute
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2
      hR2_pos hmeasure_surge_acceptAll_pos
      D.forms D.local_endpoint
  exact
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements_from_exists
      μ arrival m z switch12 switch21 S.forms
      S.nonsurge_reject_long_improvement
      S.nonsurge_accept_middle_improvement
      S.surge_reject_short_improvement
      S.surge_reject_middle_improvement

/--
Theorem 4 AE endpoint from the scalar surge-cutoff middle-cutoff-reroute
boundary.  The scalar cutoff package lowers to the by-policy-form endpoint
certificate before the same rejected-mass Theorem 4 proof is applied.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_surge_cutoff_by_policy_form_middle_cutoff_reroute_source_existence
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3FixedResponsePolicyFormSurgeCutoffByPolicyFormMiddleCutoffRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_by_policy_form_middle_cutoff_reroute_source_existence
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2 hR2_pos
    hmeasure_surge_acceptAll_pos
    D.to_by_policy_form_source

end

end GN21DriverSurgePricing
