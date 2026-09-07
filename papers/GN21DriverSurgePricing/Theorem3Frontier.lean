import GN21DriverSurgePricing.Theorem4Frontier

/-!
# Theorem 3 Frontier Routes for Driver Surge Pricing

This file holds the active small-surge Theorem 3 endpoints that are closest to
the source proof path.  Keeping them outside `MainTheorems.lean` gives future
proof work a narrow build target while the large CTMC theorem ledger remains
stable.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/-!
The current paper-proof route is the small-surge sequential construction:
choose surge prices with slack, move surge to accept-all first, then apply the
non-surge Lemma 10 comparison after the surge state is fixed at accept-all.
Do not use the finite/infinite pointwise upper-transfer branch as the default
source route; the CTMC reject-long monotonicity naturally gives the opposite
pointwise comparison unless an extra source upper/equality assumption is
available.

When Lemma 5 only identifies policy forms up to a.e. representatives, the
source-faithful boundary remains the fixed-response/bracket LightAE route in
`MainTheorems.lean`: it proves strict improvement on canonical representatives
and transfers back by a.e. congruence.  This frontier file adds a
feasible-canonical shortcut for sources that can provide the stronger
policy-level canonical-dominance data directly.  The finite-or-infinite
aggregate-cross route remains useful when the source proof really has exact
branch selectors for the current policy representatives.  It keeps the paper's
`t = infinity` non-surge convention, derives scalar ratio bookkeeping from
normalized trip-length laws, and asks for aggregate cross-ratio endpoint fields
rather than the misleading pointwise upper-transfer field.
-/

/--
Policy-level Lemma 5 canonical-dominance data instantiate the LightAE
middle-reroute existence boundary.  This is the representative/a.e. route to
use when Lemma 5 proves canonical replacements for every measurable optimum,
but does not justify exact pointwise finite-or-infinite branch syntax for the
original policy representative.
-/
noncomputable def GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData.of_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurablePolicyCanonicalDominanceData μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (local_endpoint :
      Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  replacement := D.to_allowed_replacement_data
  local_endpoint := local_endpoint

/--
Feasible-seed Lemma 5 canonical-dominance data instantiate the same LightAE
middle-reroute existence boundary.  This is usually the closest Lean target to
the continuous Lemma 5 proof, because the replacement policy is already paired
with feasibility and measurability of the updated dynamic policy.
-/
noncomputable def GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData.of_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (local_endpoint :
      Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  replacement := D.to_allowed_replacement_data
  local_endpoint := local_endpoint

/--
Per-price payload for the LightAE feasible-canonical frontier: Lemma 5
canonical dominance gives the replacement package, while the local endpoint
certificate supplies the fixed-state middle-reroute strict move.
-/
structure GN21Theorem3LightAEFeasibleCanonicalEndpointData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  canonical :
    Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
  local_endpoint :
    Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate
      μ arrival R1 R2 switch12 switch21 m z

/--
Theorem 4 AE endpoint directly from the LightAE feasible-canonical payload.
This is the fixed-price form of the source proof boundary: feasible Lemma 5
canonical dominance supplies the all-optima replacement data, and the local
middle-reroute certificate supplies the positive-rejected-mass endpoint moves.
-/
theorem paper_theorem4_measurable_accept_all_ae_unique_optimal_of_light_ae_feasible_canonical_endpoint
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
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
      GN21Theorem3LightAEFeasibleCanonicalEndpointData
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
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_middle_reroute_light_ae_eq_source_existence
      μ arrival m z R1 R2 switch12 switch21 P hR1_pos hR1_lt_R2 hR2_pos
      hmeasure_surge_acceptAll_pos
      (GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData.of_feasible_policy_canonical_dominance
        D.canonical D.local_endpoint)

/--
Feasible policy-level Lemma 5 canonical-dominance data instantiate the
feasible a.e. representative source package used by the representative
Theorem 3 route.  The only remaining endpoint obligations are the four
source-local strict-improvement callbacks on the exact representatives.
-/
noncomputable def GN21Theorem3FeasibleAERepresentativeSourceData.of_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (forms :
      Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (accept_all_optimal :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy)
    (nonsurge_reject_long_improvement :
      ∀ ρ : Fin 2 → TripPolicy,
        (hρ :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ¬ acceptsAllTrips (ρ 0) →
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
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            gn21SurgeFeasibleStatewiseStrictAggregateImprovement
              μ arrival m z switch12 switch21 ρ) :
    GN21Theorem3FeasibleAERepresentativeSourceData
      μ arrival switch12 switch21 m z where
  forms := forms.to_allowed_policy_forms.to_feasible_ae_policy_forms
  accept_all_optimal := accept_all_optimal
  nonsurge_reject_long_improvement := nonsurge_reject_long_improvement
  nonsurge_accept_middle_improvement := nonsurge_accept_middle_improvement
  surge_reject_short_improvement := surge_reject_short_improvement
  surge_reject_middle_improvement := surge_reject_middle_improvement

/--
Per-price payload for the feasible-canonical representative route: Lemma 5
canonical dominance gives the a.e. policy-form representatives, while the four
endpoint callbacks rule out each non-accept-all representative branch.
-/
structure GN21Theorem3FeasibleCanonicalRepresentativeEndpointData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  canonical :
    Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
  accept_all_optimal :
    dynamicMeasurableOptimal
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
      acceptAllDynamicPolicy
  nonsurge_reject_long_improvement :
    ∀ ρ : Fin 2 → TripPolicy,
      (hρ :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ¬ acceptsAllTrips (ρ 0) →
      ∀ t : ℝ,
        rejectsLongTrips t (ρ 0) →
          gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
            μ arrival m z switch12 switch21 ρ
  nonsurge_accept_middle_improvement :
    ∀ ρ : Fin 2 → TripPolicy,
      (hρ :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ¬ acceptsAllTrips (ρ 0) →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement
            μ arrival m z switch12 switch21 ρ
  surge_reject_short_improvement :
    ∀ ρ : Fin 2 → TripPolicy,
      (hρ :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ¬ acceptsAllTrips (ρ 1) →
      ∀ t : ℝ,
        rejectsShortTrips t (ρ 1) →
          gn21SurgeFeasibleStatewiseStrictAggregateImprovement
            μ arrival m z switch12 switch21 ρ
  surge_reject_middle_improvement :
    ∀ ρ : Fin 2 → TripPolicy,
      (hρ :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ¬ acceptsAllTrips (ρ 1) →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          gn21SurgeFeasibleStatewiseStrictAggregateImprovement
            μ arrival m z switch12 switch21 ρ

/-- Convert the feasible-canonical representative payload to the source data
consumed by the existing feasible a.e. representative Theorem 3 route. -/
noncomputable def GN21Theorem3FeasibleCanonicalRepresentativeEndpointData.to_feasible_ae_representative_source
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      GN21Theorem3FeasibleCanonicalRepresentativeEndpointData
        μ arrival switch12 switch21 m z) :
    GN21Theorem3FeasibleAERepresentativeSourceData
      μ arrival switch12 switch21 m z :=
  GN21Theorem3FeasibleAERepresentativeSourceData.of_feasible_policy_canonical_dominance
    D.canonical D.accept_all_optimal D.nonsurge_reject_long_improvement
    D.nonsurge_accept_middle_improvement D.surge_reject_short_improvement
    D.surge_reject_middle_improvement

/--
Normalized-mass feasible-canonical representative route for Theorem 3.  This
is the a.e.-representative version of the paper path when Lemma 5 has been
closed by feasible policy-canonical dominance rather than by fixed-response
one-threshold records.
-/
theorem theorem3_measurable_ic_ae_unique_of_feasible_policy_canonical_representative_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (endpoint_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FeasibleCanonicalRepresentativeEndpointData
            μ arrival switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
    paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_ae_representative_ratio_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      (measure_pos_of_singleStateTripMass_eq_one (μ 0) acceptAllPolicy
        hmass1_eq_one)
      (measure_pos_of_singleStateTripMass_eq_one (μ 1) acceptAllPolicy
        hmass2_eq_one)
      (fun m z hnonneg hparams =>
        (endpoint_selection m z hnonneg hparams).to_feasible_ae_representative_source)

/-- IC projection of the feasible-canonical representative normalized route. -/
theorem theorem3_measurable_ic_of_feasible_policy_canonical_representative_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (endpoint_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FeasibleCanonicalRepresentativeEndpointData
            μ arrival switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
      (theorem3_measurable_ic_ae_unique_of_feasible_policy_canonical_representative_normalized_mass_ratio_source
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
        hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        htime1_integrable htime2_integrable hq1_integrable hq2_integrable
        hmass1_eq_one hmass2_eq_one endpoint_selection)

/--
Theorem 3 on the normalized-mass LightAE route, with the per-price proof
payload stated as feasible Lemma 5 canonical dominance plus the fixed-state
middle-reroute endpoint certificate.  Use this shortcut only when the source
proof can supply the stronger policy-level canonical-dominance data directly;
otherwise use the fixed-response/bracket LightAE route that works with a.e.
representatives.
-/
theorem theorem3_measurable_ic_ae_unique_of_light_ae_feasible_canonical_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (endpoint_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3LightAEFeasibleCanonicalEndpointData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
    paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_light_ae_existence_normalized_mass_ratio_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one
      (by
        intro m z hnonneg hparams
        let S := endpoint_selection m z hnonneg hparams
        exact
          GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData.of_feasible_policy_canonical_dominance
            S.canonical S.local_endpoint)

/-- IC projection of the LightAE feasible-canonical normalized route. -/
theorem theorem3_measurable_ic_of_light_ae_feasible_canonical_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (endpoint_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3LightAEFeasibleCanonicalEndpointData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
      (theorem3_measurable_ic_ae_unique_of_light_ae_feasible_canonical_normalized_mass_ratio_source
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
        hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        htime1_integrable htime2_integrable hq1_integrable hq2_integrable
        hmass1_eq_one hmass2_eq_one endpoint_selection)

/--
Theorem 3 on the bracket fixed-response LightAE route, with positive
accept-all mass derived from normalized trip-length laws.  This is the compact
frontier for the main a.e.-representative proof path: Lemma 5 remains at the
bracket fixed-response level, and endpoint work uses the common fixed-state
middle-reroute certificate.
-/
theorem theorem3_measurable_ic_ae_unique_of_bracket_light_ae_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketEqMiddleRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
    paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_eq_middle_reroute_existence_ratio_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      (measure_pos_of_singleStateTripMass_eq_one (μ 0) acceptAllPolicy
        hmass1_eq_one)
      (measure_pos_of_singleStateTripMass_eq_one (μ 1) acceptAllPolicy
        hmass2_eq_one)
      fixed_response_selection

/-- IC projection of the normalized bracket fixed-response LightAE route. -/
theorem theorem3_measurable_ic_of_bracket_light_ae_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketEqMiddleRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
      (theorem3_measurable_ic_ae_unique_of_bracket_light_ae_normalized_mass_ratio_source
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
        hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        htime1_integrable htime2_integrable hq1_integrable hq2_integrable
        hmass1_eq_one hmass2_eq_one fixed_response_selection)

/--
Build the bracket LightAE aggregate-cross source package directly from
Lemma 6 bracket records, fixed reward-rate identities, and the paper's
aggregate fixed-state cross-ratio fields.
-/
def GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_fixed_reward_rate_cross_fields
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) =
          R1 * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (surge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 1) =
          R2 * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
    (surge_reject_short_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsShortTrips u (ρ 1) →
          gn21AcceptAllScaledStateTime (μ 1) (arrival 1) *
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) ≤
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
              gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12)
    (surge_reject_middle_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          gn21AcceptAllScaledStateTime (μ 1) (arrival 1) *
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) ≤
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
              gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21)
    (nonsurge_accept_middle_lower_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21 ≤
            gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0))
    (nonsurge_accept_middle_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  forms := forms
  local_endpoint :=
    Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateCrossByPolicyFormDerivedTailMiddleCutoffRerouteAELocalEndpointCertificate.of_one_threshold_fixed_response_cross_fields
      forms.exists_optimal
      (by
        intro ρ hopt
        exact
          (forms.nonsurge ρ hopt).to_source_data forms.hswitch12_pos
            (add_pos forms.hswitch12_pos forms.hswitch21_pos))
      (by
        intro ρ hopt
        exact
          (forms.surge ρ hopt).to_source_data forms.hswitch21_pos
            (add_pos forms.hswitch21_pos forms.hswitch12_pos))
      shared nonsurge_fixed_reward_rate surge_fixed_reward_rate
      surge_reject_short_cross surge_reject_middle_cross
      nonsurge_reject_long_upper_cross
      nonsurge_accept_middle_lower_cross nonsurge_accept_middle_upper_cross

/--
Named-rate version of the bracket LightAE aggregate-cross constructor.  This
matches the paper's Lemma 6 reward-rate notation (`Ri = R1`, `Rj = R2`) and
derives the fixed reward-rate equalities consumed by the endpoint certificate.
-/
def GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_named_rate_cross_fields
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_Ri_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.nonsurge ρ hopt).Ri = R1)
    (surge_Rj_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.surge ρ hopt).Rj = R2)
    (surge_reject_short_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsShortTrips u (ρ 1) →
          gn21AcceptAllScaledStateTime (μ 1) (arrival 1) *
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) ≤
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
              gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12)
    (surge_reject_middle_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          gn21AcceptAllScaledStateTime (μ 1) (arrival 1) *
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) ≤
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
              gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21)
    (nonsurge_accept_middle_lower_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21 ≤
            gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0))
    (nonsurge_accept_middle_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_fixed_reward_rate_cross_fields
    forms shared
    (by
      intro ρ hopt
      exact
        (forms.nonsurge ρ hopt).fixed_reward_rate_of_Ri_eq
          (nonsurge_Ri_eq ρ hopt))
    (by
      intro ρ hopt
      exact
        (forms.surge ρ hopt).fixed_reward_rate_of_Rj_eq
          (surge_Rj_eq ρ hopt))
    surge_reject_short_cross surge_reject_middle_cross
    nonsurge_reject_long_upper_cross
    nonsurge_accept_middle_lower_cross nonsurge_accept_middle_upper_cross

/--
Named-rate bracket LightAE aggregate-cross package from the paper's surge
cutoff bounds.  The shared CTMC monotonicity lemmas integrate the short- and
middle-rejection scalar cutoff inequalities into the aggregate surge
cross-ratio fields.
-/
def GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_named_rate_surge_cutoff_bounds
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_Ri_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.nonsurge ρ hopt).Ri = R1)
    (surge_Rj_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.surge ρ hopt).Rj = R2)
    (surge_reject_short_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ u : ℝ,
          rejectsShortTrips u (ρ 1) →
            0 < u →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * u ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 u)
    (surge_reject_middle_ordered_upper_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            lo ≤ hi →
              0 < hi →
                gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                    (ρ 1) * hi ≤
                  gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                    gn21SwitchProb switch21 switch12 hi)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21)
    (nonsurge_accept_middle_lower_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21 ≤
            gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0))
    (nonsurge_accept_middle_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_named_rate_cross_fields
    forms shared nonsurge_Ri_eq surge_Rj_eq
    (by
      intro ρ hopt u hshape
      exact
        shared.surge_fixed_cross_le_acceptAll_of_rejectsShortTrips_of_positive_cutoff_bound
          hopt.1 hshape
          (surge_reject_short_cutoff_bound ρ hopt u hshape))
    (by
      intro ρ hopt lo hi hshape
      exact
        shared.surge_fixed_cross_le_acceptAll_of_rejectsMiddleTrips_of_ordered_positive_upper_cutoff_bound
          hopt.1 hshape
          (surge_reject_middle_ordered_upper_cutoff_bound ρ hopt lo hi
            hshape))
    nonsurge_reject_long_upper_cross
    nonsurge_accept_middle_lower_cross nonsurge_accept_middle_upper_cross

/--
For the bracket one-threshold non-surge fixed-response branch, Lemma 5 gives a
reject-long representative up to a.e. equality.  A reject-long upper
cross-ratio bound on that representative transfers back to the raw policy and
also supplies the lower cross-ratio bound needed by the middle-reroute endpoint
adapter.  This is the key bridge that prevents the Theorem 3 frontier from
asking for separate non-surge accept-middle cross assumptions that are not part
of the one-threshold paper route.
-/
theorem Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData.nonsurge_ae_rejectLong_cross_pair
    {μ : Fin 2 → Measure TripLength}
    [NoAtoms (μ 0)]
    {arrival m z : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21)
    (ρ : Fin 2 → TripPolicy)
    (hopt :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ) :
    gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
        gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 ≤
      gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) ∧
    gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) ≤
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
        gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 := by
  let hsum : 0 < switch12 + switch21 :=
    add_pos forms.hswitch12_pos forms.hswitch21_pos
  let source :
      GN21MeasuredLeftFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ
        .strictlyDecreasing :=
    (forms.nonsurge ρ hopt).to_source_data forms.hswitch12_pos hsum
  let fixed :
      Lemma5FixedResponsePolicyFormFeasibleOptimalData (μ 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1)) .strictlyDecreasing (ρ 0) :=
    source.to_fixed_response hopt
  let rep :
      Lemma5FeasiblePolicyFormAlmostEverywhereData (μ 0)
        .strictlyDecreasing (ρ 0) :=
    fixed.to_feasiblePolicyFormAlmostEverywhere (hopt.1 0).2 (hopt.1 0).1
  have hrep_form : ∃ u : ℝ, rejectsLongTrips u rep.policy := by
    have hpolicy_form := rep.policy_form
    change ∃ u : ℝ, rejectsLongTrips u rep.policy at hpolicy_form
    exact hpolicy_form
  rcases hrep_form with ⟨u, hrep_shape⟩
  let ρrep : Fin 2 → TripPolicy := Function.update ρ 0 rep.policy
  have hρrep :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρrep :=
    dynamicMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_zero_of_policy_ae
      μ arrival switch12 switch21
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
      hopt rep.policy_subset rep.policy_measurable rep.policy_ae
  have hrep_shape_update : rejectsLongTrips u (ρrep 0) := by
    simpa [ρrep, Function.update] using hrep_shape
  have hlower_rep :
      gn21ScaledStateTime (μ 0) (arrival 0) rep.policy *
          gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 ≤
        gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
          gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            rep.policy := by
    simpa [ρrep, Function.update] using
      shared.nonsurge_fixed_cross_ge_acceptAll_of_rejectsLongTrips
        hρrep.1 hrep_shape_update
  have hupper_rep :
      gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
          gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            rep.policy ≤
        gn21ScaledStateTime (μ 0) (arrival 0) rep.policy *
          gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
            switch12 switch21 := by
    simpa [ρrep, Function.update] using
      nonsurge_reject_long_upper_cross ρrep hρrep u hrep_shape_update
  have htime :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) =
        gn21ScaledStateTime (μ 0) (arrival 0) rep.policy :=
    gn21ScaledStateTime_congr_policy_ae (μ 0) (arrival 0) rep.policy_ae
  have hq :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) =
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
          rep.policy :=
    gn21ExitWeightIntegral_congr_policy_ae (μ 0) (arrival 0) switch12
      switch21 rep.policy_ae
  exact
    ⟨by simpa [htime, hq] using hlower_rep,
      by simpa [htime, hq] using hupper_rep⟩

/--
Named-rate bracket LightAE aggregate-cross package from the paper's surge
cutoff bounds and only the non-surge reject-long upper cross comparison.  The
non-surge accept-middle cross fields are derived from the a.e. reject-long
representative supplied by the one-threshold fixed-response data.
-/
def GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_named_rate_surge_cutoff_bounds_reject_long_upper
    {μ : Fin 2 → Measure TripLength}
    [NoAtoms (μ 0)]
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_Ri_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.nonsurge ρ hopt).Ri = R1)
    (surge_Rj_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.surge ρ hopt).Rj = R2)
    (surge_reject_short_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ u : ℝ,
          rejectsShortTrips u (ρ 1) →
            0 < u →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * u ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 u)
    (surge_reject_middle_ordered_upper_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            lo ≤ hi →
              0 < hi →
                gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                    (ρ 1) * hi ≤
                  gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                    gn21SwitchProb switch21 switch12 hi)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_named_rate_surge_cutoff_bounds
    forms shared nonsurge_Ri_eq surge_Rj_eq
    surge_reject_short_cutoff_bound
    surge_reject_middle_ordered_upper_cutoff_bound
    nonsurge_reject_long_upper_cross
    (by
      intro ρ hopt _lo _hi _hshape
      exact
        (forms.nonsurge_ae_rejectLong_cross_pair shared
          nonsurge_reject_long_upper_cross ρ hopt).1)
    (by
      intro ρ hopt _lo _hi _hshape
      exact
        (forms.nonsurge_ae_rejectLong_cross_pair shared
          nonsurge_reject_long_upper_cross ρ hopt).2)

/--
Bracket fixed-response source package for the paper route after the a.e.
representative bridge.  Compared with the aggregate-cross middle-cutoff source
boundary, this source data no longer asks for separate non-surge accept-middle
cross fields; Lean derives them from the reject-long representative.
-/
structure GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  forms :
    Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
      μ arrival switch12 switch21 m z
  shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21
  nonsurge_Ri_eq :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
        (forms.nonsurge ρ hopt).Ri = R1
  surge_Rj_eq :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
        (forms.surge ρ hopt).Rj = R2
  surge_reject_short_cutoff_bound :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ∀ u : ℝ,
        rejectsShortTrips u (ρ 1) →
          0 < u →
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) * u ≤
              gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                gn21SwitchProb switch21 switch12 u
  surge_reject_middle_ordered_upper_cutoff_bound :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          lo ≤ hi →
            0 < hi →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * hi ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 hi
  nonsurge_reject_long_upper_cross :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21

/--
Bracket fixed-response source package with the paper-style one-sided
pointwise upper transfer on rejected non-surge trips.  This is weaker than
pointwise equality and stronger/more local than the already-integrated
aggregate reject-long upper cross field.
-/
structure GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffPointwiseUpperSourceExistenceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  forms :
    Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
      μ arrival switch12 switch21 m z
  shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21
  nonsurge_Ri_eq :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
        (forms.nonsurge ρ hopt).Ri = R1
  surge_Rj_eq :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
        (forms.surge ρ hopt).Rj = R2
  surge_reject_short_cutoff_bound :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ∀ u : ℝ,
        rejectsShortTrips u (ρ 1) →
          0 < u →
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) * u ≤
              gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                gn21SwitchProb switch21 switch12 u
  surge_reject_middle_ordered_upper_cutoff_bound :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          lo ≤ hi →
            0 < hi →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * hi ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 hi
  nonsurge_reject_long_pointwise_upper_transfer :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          ∀ τ ∈ acceptAllPolicy \ ρ 0,
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) * τ ≤
              gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
                gn21SwitchProb switch12 switch21 τ

/--
The reduced bracket source package instantiates the aggregate-cross
middle-cutoff source boundary by deriving the non-surge accept-middle cross
fields from the a.e. reject-long representative.
-/
noncomputable def GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData.to_middle_cutoff_source
    {μ : Fin 2 → Measure TripLength}
    [NoAtoms (μ 0)]
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (D :
      GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData.of_named_rate_surge_cutoff_bounds_reject_long_upper
    D.forms D.shared D.nonsurge_Ri_eq D.surge_Rj_eq
    D.surge_reject_short_cutoff_bound
    D.surge_reject_middle_ordered_upper_cutoff_bound
    D.nonsurge_reject_long_upper_cross

/--
Build the reduced bracket reject-long-upper package from target fixed
reward-rate identities.  This removes the local `Ri = R1` and `Rj = R2`
bookkeeping fields from the main reduced route while keeping the source
obligations in the paper's reward-rate form.
-/
noncomputable def GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData.of_fixed_reward_rate_fields
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (surge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
          R2 * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
    (surge_reject_short_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ u : ℝ,
          rejectsShortTrips u (ρ 1) →
            0 < u →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * u ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 u)
    (surge_reject_middle_ordered_upper_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            lo ≤ hi →
              0 < hi →
                gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                    (ρ 1) * hi ≤
                  gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                    gn21SwitchProb switch21 switch12 hi)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  forms := forms
  shared := shared
  nonsurge_Ri_eq := by
    intro ρ hopt
    exact
      (forms.nonsurge ρ hopt).Ri_eq_of_fixed_reward_rate
        (nonsurge_fixed_reward_rate ρ hopt)
  surge_Rj_eq := by
    intro ρ hopt
    exact
      (forms.surge ρ hopt).Rj_eq_of_fixed_reward_rate
        (surge_fixed_reward_rate ρ hopt)
  surge_reject_short_cutoff_bound := surge_reject_short_cutoff_bound
  surge_reject_middle_ordered_upper_cutoff_bound :=
    surge_reject_middle_ordered_upper_cutoff_bound
  nonsurge_reject_long_upper_cross := nonsurge_reject_long_upper_cross

/--
Reduced bracket source payload with fixed reward-rate identities instead of
local `Ri`/`Rj` name equalities.  This is the source-facing version of the
reject-long-upper route.
-/
structure GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffFixedRewardRateRejectLongUpperSourceExistenceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  forms :
    Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
      μ arrival switch12 switch21 m z
  shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21
  nonsurge_fixed_reward_rate :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      gn21ScaledStateEarning (μ 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
        R1 * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0)
  surge_fixed_reward_rate :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      gn21ScaledStateEarning (μ 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        R2 * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1)
  surge_reject_short_cutoff_bound :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ∀ u : ℝ,
        rejectsShortTrips u (ρ 1) →
          0 < u →
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) * u ≤
              gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                gn21SwitchProb switch21 switch12 u
  surge_reject_middle_ordered_upper_cutoff_bound :
    ∀ ρ : Fin 2 → TripPolicy,
      (hopt :
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ) →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          lo ≤ hi →
            0 < hi →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * hi ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 hi
  nonsurge_reject_long_upper_cross :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21

/--
Convert the source-facing fixed-reward-rate payload to the reduced
reject-long-upper source package by canceling the positive current times in
the bracket records.
-/
noncomputable def GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffFixedRewardRateRejectLongUpperSourceExistenceData.to_reject_long_upper_source
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (D :
      GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffFixedRewardRateRejectLongUpperSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData.of_fixed_reward_rate_fields
    D.forms D.shared D.nonsurge_fixed_reward_rate D.surge_fixed_reward_rate
    D.surge_reject_short_cutoff_bound
    D.surge_reject_middle_ordered_upper_cutoff_bound
    D.nonsurge_reject_long_upper_cross

/--
The older bracket ordered-cross-field source boundary is stronger than the
reduced fixed-reward-rate LightAE boundary: it also carries the non-surge
accept-middle cross fields.  Forget those extra fields before using the reduced
route, where Lean reconstructs the accept-middle side from the reject-long
representative.
-/
noncomputable def GN21Theorem3FixedResponseOneThresholdBracketOrderedSurgeCutoffCrossFieldMiddleCutoffRerouteSourceExistenceData.to_fixed_reward_rate_reject_long_upper_source
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (D :
      GN21Theorem3FixedResponseOneThresholdBracketOrderedSurgeCutoffCrossFieldMiddleCutoffRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffFixedRewardRateRejectLongUpperSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  forms := D.forms
  shared := D.shared
  nonsurge_fixed_reward_rate := D.nonsurge_fixed_reward_rate
  surge_fixed_reward_rate := D.surge_fixed_reward_rate
  surge_reject_short_cutoff_bound := D.surge_reject_short_cutoff_bound
  surge_reject_middle_ordered_upper_cutoff_bound :=
    D.surge_reject_middle_ordered_upper_cutoff_bound
  nonsurge_reject_long_upper_cross := D.nonsurge_reject_long_upper_cross

/--
Bracket-level exact one-threshold branch source data feed the reduced
fixed-reward-rate LightAE route through the ordered cross-field adapter.  This
keeps the exact-branch proof path available without restating the non-surge
accept-middle cross fields at the reduced boundary.
-/
noncomputable def GN21Theorem3FixedResponseExactOneThresholdBracketBranchByPolicyFormMiddleCutoffRerouteSourceExistenceData.to_fixed_reward_rate_reject_long_upper_source
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (D :
      GN21Theorem3FixedResponseExactOneThresholdBracketBranchByPolicyFormMiddleCutoffRerouteSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffFixedRewardRateRejectLongUpperSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  D.to_bracket_ordered_surge_cutoff_cross_field_source.to_fixed_reward_rate_reject_long_upper_source

/--
Build the reduced bracket source package from the paper-style one-sided
pointwise upper transfer on rejected non-surge trips.  The pointwise comparison
is integrated once, here, into the aggregate reject-long upper cross field.
-/
noncomputable def GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData.of_pointwise_upper_transfer
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_Ri_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.nonsurge ρ hopt).Ri = R1)
    (surge_Rj_eq :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
          (forms.surge ρ hopt).Rj = R2)
    (surge_reject_short_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ u : ℝ,
          rejectsShortTrips u (ρ 1) →
            0 < u →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * u ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 u)
    (surge_reject_middle_ordered_upper_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        (hopt :
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ) →
        ∀ lo hi : ℝ,
          rejectsMiddleTrips lo hi (ρ 1) →
            lo ≤ hi →
              0 < hi →
                gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                    (ρ 1) * hi ≤
                  gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                    gn21SwitchProb switch21 switch12 hi)
    (nonsurge_reject_long_pointwise_upper_transfer :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          ∀ τ ∈ acceptAllPolicy \ ρ 0,
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) * τ ≤
              gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
                gn21SwitchProb switch12 switch21 τ) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  forms := forms
  shared := shared
  nonsurge_Ri_eq := nonsurge_Ri_eq
  surge_Rj_eq := surge_Rj_eq
  surge_reject_short_cutoff_bound := surge_reject_short_cutoff_bound
  surge_reject_middle_ordered_upper_cutoff_bound :=
    surge_reject_middle_ordered_upper_cutoff_bound
  nonsurge_reject_long_upper_cross := by
    intro ρ hopt u hshape
    exact
      shared.nonsurge_fixed_cross_le_acceptAll_of_complement_pointwise
        hopt.1
        (nonsurge_reject_long_pointwise_upper_transfer ρ hopt u hshape)

/--
The pointwise-upper source package instantiates the reduced aggregate source
by integrating the pointwise non-surge transfer comparison.
-/
noncomputable def GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffPointwiseUpperSourceExistenceData.to_reject_long_upper_source
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (D :
      GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffPointwiseUpperSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData.of_pointwise_upper_transfer
    D.forms D.shared D.nonsurge_Ri_eq D.surge_Rj_eq
    D.surge_reject_short_cutoff_bound
    D.surge_reject_middle_ordered_upper_cutoff_bound
    D.nonsurge_reject_long_pointwise_upper_transfer

/--
Theorem 3 on the bracket fixed-response LightAE route with aggregate
cross-ratio endpoint data and normalized trip-length laws.  This is the
closest current frontier to the paper proof when Lemma 9/10 provide aggregate
ratio comparisons rather than pointwise fixed-transfer equalities.
-/
theorem theorem3_measurable_ic_ae_unique_of_bracket_surge_cross_middle_cutoff_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  have hmeasure1_pos : 0 < μ 0 acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_eq_one (μ 0) acceptAllPolicy
      hmass1_eq_one
  have hmeasure2_pos : 0 < μ 1 acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_eq_one (μ 1) acceptAllPolicy
      hmass2_eq_one
  rcases theorem3_acceptAll_ratio_source_scalar_consequences
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      rho R1 R2 hR1_eq hR2_pos hC_lt_rho hrho_lt_one
      harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable hq1_integrable hmeasure1_pos with
    ⟨_, hR1_pos, hR1_lt_R2⟩
  exact
    paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cross_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
      μ arrival rho R1 R2 switch12 switch21
      { hR1_eq := hR1_eq
        hR1_pos := hR1_pos
        hR1_lt_R2 := hR1_lt_R2
        hR2_pos := hR2_pos
        hC_lt_rho := hC_lt_rho
        hrho_lt_one := hrho_lt_one
        harrival1_pos := harrival1_pos
        harrival2_pos := harrival2_pos
        hswitch12_pos := hswitch12_pos
        hswitch21_pos := hswitch21_pos
        htime1_integrable := htime1_integrable
        htime2_integrable := htime2_integrable
        hq1_integrable := hq1_integrable
        hq2_integrable := hq2_integrable
        hmeasure1_pos := hmeasure1_pos
        hmeasure2_pos := hmeasure2_pos
        fixed_response_one_threshold_bracket_surge_cross_by_policy_form_middle_cutoff_reroute_existence_selection :=         fixed_response_selection }

/-- IC projection of the normalized bracket aggregate-cross middle-cutoff route. -/
theorem theorem3_measurable_ic_of_bracket_surge_cross_middle_cutoff_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCrossByPolicyFormMiddleCutoffRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
      (theorem3_measurable_ic_ae_unique_of_bracket_surge_cross_middle_cutoff_normalized_mass_ratio_source
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
        hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        htime1_integrable htime2_integrable hq1_integrable hq2_integrable
        hmass1_eq_one hmass2_eq_one fixed_response_selection)

/--
Theorem 3 on the reduced bracket surge-cutoff/reject-long-upper source route.
This is the current paper-proof frontier: the only remaining non-surge
cross-ratio source field is the reject-long upper comparison; Lean derives the
lower comparison and the accept-middle adapter fields internally.
-/
theorem theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_reject_long_upper_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3_measurable_ic_ae_unique_of_bracket_surge_cross_middle_cutoff_normalized_mass_ratio_source
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (by
      intro m z hnonneg hparams
      exact
        (fixed_response_selection m z hnonneg hparams).to_middle_cutoff_source)

/--
Theorem 3 on the reduced bracket route with fixed reward-rate identities.
This is the source-facing version of the reject-long-upper frontier: Lean
derives the local `Ri = R1` and `Rj = R2` names from the fixed reward rates.
-/
theorem theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffFixedRewardRateRejectLongUpperSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_reject_long_upper_normalized_mass_ratio_source
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (by
      intro m z hnonneg hparams
      exact
        (fixed_response_selection m z hnonneg hparams).to_reject_long_upper_source)

/-- IC projection of the reduced bracket surge-cutoff/reject-long-upper route. -/
theorem theorem3_measurable_ic_of_bracket_surge_cutoff_reject_long_upper_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffRejectLongUpperSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
    (theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_reject_long_upper_normalized_mass_ratio_source
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one fixed_response_selection)

/-- IC projection of the fixed-reward-rate reduced bracket route. -/
theorem theorem3_measurable_ic_of_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffFixedRewardRateRejectLongUpperSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
    (theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_mass_ratio_source
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one fixed_response_selection)

/--
Theorem 3 on the bracket ordered cross-field route, lowered through the reduced
fixed-reward-rate LightAE boundary.  This proves that the older source package
with explicit non-surge accept-middle cross fields is stronger than the reduced
reject-long-upper route.
-/
theorem theorem3_measurable_ic_ae_unique_of_bracket_ordered_cross_field_light_ae_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketOrderedSurgeCutoffCrossFieldMiddleCutoffRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_mass_ratio_source
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (by
      intro m z hnonneg hparams
      exact
        (fixed_response_selection m z hnonneg hparams).to_fixed_reward_rate_reject_long_upper_source)

/-- IC projection of the bracket ordered cross-field LightAE route. -/
theorem theorem3_measurable_ic_of_bracket_ordered_cross_field_light_ae_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketOrderedSurgeCutoffCrossFieldMiddleCutoffRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
    (theorem3_measurable_ic_ae_unique_of_bracket_ordered_cross_field_light_ae_normalized_mass_ratio_source
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one fixed_response_selection)

/--
The exact bracket one-threshold branch data feed the reduced LightAE route
through the ordered-cross-field adapter.
-/
theorem theorem3_measurable_ic_ae_unique_of_exact_bracket_branch_light_ae_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseExactOneThresholdBracketBranchByPolicyFormMiddleCutoffRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_mass_ratio_source
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (by
      intro m z hnonneg hparams
      exact
        (fixed_response_selection m z hnonneg hparams).to_fixed_reward_rate_reject_long_upper_source)

/-- IC projection of the exact bracket one-threshold LightAE route. -/
theorem theorem3_measurable_ic_of_exact_bracket_branch_light_ae_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseExactOneThresholdBracketBranchByPolicyFormMiddleCutoffRerouteSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
    (theorem3_measurable_ic_ae_unique_of_exact_bracket_branch_light_ae_normalized_mass_ratio_source
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one fixed_response_selection)

/--
Theorem 3 on the reduced bracket surge-cutoff route with the non-surge
reject-long field supplied as a one-sided pointwise upper transfer on rejected
trips.
-/
theorem theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_pointwise_upper_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffPointwiseUpperSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_reject_long_upper_normalized_mass_ratio_source
    μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
    hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
    htime1_integrable htime2_integrable hq1_integrable hq2_integrable
    hmass1_eq_one hmass2_eq_one
    (by
      intro m z hnonneg hparams
      exact
        (fixed_response_selection m z hnonneg hparams).to_reject_long_upper_source)

/-- IC projection of the reduced bracket pointwise-upper route. -/
theorem theorem3_measurable_ic_of_bracket_surge_cutoff_pointwise_upper_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (fixed_response_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3FixedResponseOneThresholdBracketSurgeCutoffPointwiseUpperSourceExistenceData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
    (theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_pointwise_upper_normalized_mass_ratio_source
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one fixed_response_selection)

/--
Build the finite-or-infinite aggregate-cross named-rate package from fixed
reward-rate identities.  This keeps the source-facing Theorem 3 route on the
paper's reward-rate equations and derives the local Lemma 6 names internally.
-/
def GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData.of_fixed_reward_rate_fields
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (nonsurge_reject_long_finite_or_infinite :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        rejectsLongTripsFiniteOrInfiniteCutoff (ρ 0))
    (surge_reject_short_shape :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        ∃ u : ℝ, rejectsShortTrips u (ρ 1))
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) =
          R1 * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (surge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 1) =
          R2 * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
    (surge_reject_short_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsShortTrips u (ρ 1) →
          0 < u →
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) * u ≤
              gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                gn21SwitchProb switch21 switch12 u)
    (surge_reject_middle_ordered_upper_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          lo ≤ hi →
            0 < hi →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * hi ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 hi)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21)
    (nonsurge_accept_middle_lower_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21 ≤
            gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0))
    (nonsurge_accept_middle_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21) :
    GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData.of_surge_cutoff_bounds
    forms
    nonsurge_reject_long_finite_or_infinite
    surge_reject_short_shape
    shared
    (by
      intro ρ hopt
      exact
        (forms.nonsurge ρ hopt).Ri_eq_of_fixed_reward_rate
          (nonsurge_fixed_reward_rate ρ hopt))
    (by
      intro ρ hopt
      exact
        (forms.surge ρ hopt).Rj_eq_of_fixed_reward_rate
          (surge_fixed_reward_rate ρ hopt))
    surge_reject_short_cutoff_bound
    surge_reject_middle_ordered_upper_cutoff_bound
    nonsurge_reject_long_upper_cross
    nonsurge_accept_middle_lower_cross
    nonsurge_accept_middle_upper_cross

/--
Theorem 3 AE uniqueness on the finite-or-infinite aggregate-cross route.  Use
this branch-selection frontier when the proof has exact finite-cutoff or
accept-all selectors for the current policy representatives; use the LightAE
feasible-canonical route above when Lemma 5 supplies those forms only up to
a.e. representative replacement.
-/
theorem theorem3_measurable_ic_ae_unique_of_finite_or_infinite_surge_cross_named_rate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (named_rate_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData
              μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
    paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_finite_or_infinite_one_threshold_branch_surge_cross_named_rate_normalized_mass_ratio_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one named_rate_selection

/-- IC projection of the finite-or-infinite aggregate-cross frontier. -/
theorem theorem3_measurable_ic_of_finite_or_infinite_surge_cross_named_rate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (named_rate_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData
              μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
      (theorem3_measurable_ic_ae_unique_of_finite_or_infinite_surge_cross_named_rate
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos
        hC_lt_rho hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos
        hswitch21_pos htime1_integrable htime2_integrable hq1_integrable
        hq2_integrable hmass1_eq_one hmass2_eq_one named_rate_selection)

/--
Normalized-mass mass-affine small-surge assumptions with no explicit `Rmax`
witness.  The source supplies the paper's ratio hypotheses, the
arrival/intercept numerator bound, accept-all lower nonpositivity, and the
fixed-state lower-cross comparison; Lean chooses the sign-selected mass-affine
envelope internally.
-/
structure Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineFixedLowerCrossNoRmaxNormalizedMassDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) where
  hR1_eq : R1 = rho * R2
  hR2_pos : 0 < R2
  hC_lt_rho :
    theorem3FeasibilityThresholdC
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch12 < rho
  hrho_lt_one : rho < 1
  harrival1_pos : 0 < arrival 0
  harrival2_pos : 0 < arrival 1
  hswitch12_pos : 0 < switch12
  hswitch21_pos : 0 < switch21
  htime1_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  htime2_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  hq1_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  hq2_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1
  hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1
  acceptAll_lower_nonpos :
    lemma9StructuredLower
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch21 ≤ 0
  arrival_nonsurge_ratio_numerator_bound :
    (arrival 0) *
        (rho * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) -
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1)) ≤
      gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
        switch12
  current_fixed_lower_cross :
    ∀ policy : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePositiveMassPolicy μ policy →
        gn21ScaledStateTime (μ 0) (arrival 0) (policy 0) *
            gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
              switch12 switch21 ≤
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
            gn21ExitWeightIntegral (μ 0) (arrival 0)
              switch12 switch21 (policy 0)

/--
Theorem 3 positive-mass measurable IC on the normalized no-`Rmax`
mass-affine fixed-lower-cross route.  This is the compact source boundary when
the paper proof uses the fixed-state cross comparison rather than a
policy-dependent Lemma 9 final-sign field.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_fixed_lower_cross_no_rmax_normalized_mass
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineFixedLowerCrossNoRmaxNormalizedMassDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  let z0 :=
    theorem3NonsurgeZRatio rho
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      switch12 * R2
  let Rmax := if z0 ≤ 0 then R2 else max R2 ((arrival 0) * z0)
  have hmass1_pos : 0 < singleStateTripMass (μ 0) acceptAllPolicy := by
    rw [A.hmass1_eq_one]
    norm_num
  have hmass2_pos : 0 < singleStateTripMass (μ 1) acceptAllPolicy := by
    rw [A.hmass2_eq_one]
    norm_num
  have hfinite1_acceptAll : (μ 0) acceptAllPolicy ≠ ⊤ :=
    singleStateTripMass_ne_top_of_eq_one A.hmass1_eq_one
  rcases theorem3_acceptAll_ratio_source_scalar_consequences
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      rho R1 R2 A.hR1_eq A.hR2_pos A.hC_lt_rho A.hrho_lt_one
      A.harrival1_pos A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
      A.htime1_integrable A.hq1_integrable
      (measure_pos_of_singleStateTripMass_pos
        (μ 0) acceptAllPolicy hmass1_pos) with
    ⟨_, hR1_pos, hR1_lt_R2⟩
  have hRmax_envelope :
      (theorem3NonsurgeZRatio rho
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
              switch12 switch21)
            switch12 * R2 ≤ 0 ∧
          Rmax = R2) ∨
        (0 ≤
            theorem3NonsurgeZRatio rho
              (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
              (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21)
              switch12 * R2 ∧
          Rmax =
            max R2
              ((arrival 0) *
                (theorem3NonsurgeZRatio rho
                  (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
                  (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                    switch12 switch21)
                  switch12 * R2))) := by
    by_cases hz0_nonpos : z0 ≤ 0
    · left
      constructor
      · simpa [z0] using hz0_nonpos
      · simp [Rmax, hz0_nonpos]
    · right
      have hz0_nonneg : 0 ≤ z0 := le_of_lt (lt_of_not_ge hz0_nonpos)
      constructor
      · simpa [z0] using hz0_nonneg
      · simp [Rmax, hz0_nonpos, z0]
  exact
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_fixed_lower_cross_arrival_bound_data_assumptions
      μ arrival rho R1 R2 switch12 switch21
      { Rmax := Rmax
        hR1_eq := A.hR1_eq
        hR1_pos := hR1_pos
        hR1_lt_R2 := hR1_lt_R2
        hR2_pos := A.hR2_pos
        hC_lt_rho := A.hC_lt_rho
        hrho_lt_one := A.hrho_lt_one
        harrival1_pos := A.harrival1_pos
        harrival2_pos := A.harrival2_pos
        hswitch12_pos := A.hswitch12_pos
        hswitch21_pos := A.hswitch21_pos
        htime1_integrable := A.htime1_integrable
        htime2_integrable := A.htime2_integrable
        hq1_integrable := A.hq1_integrable
        hq2_integrable := A.hq2_integrable
        hmass1_pos := hmass1_pos
        hmass2_pos := hmass2_pos
        hmass1_eq_one := A.hmass1_eq_one
        hfinite1_acceptAll := hfinite1_acceptAll
        acceptAll_lower_nonpos := A.acceptAll_lower_nonpos
        Rmax_envelope := hRmax_envelope
        arrival_nonsurge_ratio_numerator_bound :=
          A.arrival_nonsurge_ratio_numerator_bound
        current_fixed_lower_cross := A.current_fixed_lower_cross }

/--
Normalized no-`Rmax` fixed-lower-cross assumptions with the accept-all Lemma 9
lower endpoint stated in the paper's cross-multiplied final-sign form.
-/
structure Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineFixedLowerCrossFinalSignNoRmaxNormalizedMassDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) where
  hR1_eq : R1 = rho * R2
  hR2_pos : 0 < R2
  hC_lt_rho :
    theorem3FeasibilityThresholdC
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch12 < rho
  hrho_lt_one : rho < 1
  harrival1_pos : 0 < arrival 0
  harrival2_pos : 0 < arrival 1
  hswitch12_pos : 0 < switch12
  hswitch21_pos : 0 < switch21
  htime1_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  htime2_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  hq1_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  hq2_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1
  hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1
  acceptAll_lower_left_nonpos :
    lemma9StructuredLowerNumerator
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
          switch12 switch21)
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
          switch21 switch12)
        switch21 *
      lemma9StructuredUpperDenominator
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
          switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
          switch21 switch12)
        switch21 ≤ 0
  arrival_nonsurge_ratio_numerator_bound :
    (arrival 0) *
        (rho * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) -
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1)) ≤
      gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
        switch12
  current_fixed_lower_cross :
    ∀ policy : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePositiveMassPolicy μ policy →
        gn21ScaledStateTime (μ 0) (arrival 0) (policy 0) *
            gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
              switch12 switch21 ≤
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
            gn21ExitWeightIntegral (μ 0) (arrival 0)
              switch12 switch21 (policy 0)

/--
Theorem 3 positive-mass measurable IC on the normalized no-`Rmax`
fixed-lower-cross route with the accept-all lower endpoint derived from the
paper's cross-multiplied Lemma 9 final-sign inequality.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_fixed_lower_cross_final_sign_no_rmax_normalized_mass
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineFixedLowerCrossFinalSignNoRmaxNormalizedMassDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  have hmass1_pos : 0 < singleStateTripMass (μ 0) acceptAllPolicy := by
    rw [A.hmass1_eq_one]
    norm_num
  have hmass2_pos : 0 < singleStateTripMass (μ 1) acceptAllPolicy := by
    rw [A.hmass2_eq_one]
    norm_num
  rcases theorem3_acceptAll_measured_primitives_scalar_conditions_positive_primitives
      μ arrival switch12 switch21 A.harrival1_pos A.harrival2_pos
      A.hswitch12_pos A.hswitch21_pos A.htime1_integrable
      A.htime2_integrable A.hq1_integrable A.hq2_integrable
      (measure_pos_of_singleStateTripMass_pos
        (μ 0) acceptAllPolicy hmass1_pos)
      (measure_pos_of_singleStateTripMass_pos
        (μ 1) acceptAllPolicy hmass2_pos) with
    ⟨hT1_pos, hQ1_pos, _hQ1_sub_switch12_pos, _hden_theorem3_pos,
      hgap2_nonneg, _hT2_ge_one, hswitch21_lt_Q2⟩
  have haccept_lower_nonpos :
      lemma9StructuredLower
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch21 ≤ 0 :=
    lemma9StructuredLower_nonpos_of_positive_primitives_and_final_signs
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch21 (le_of_lt hT1_pos) hQ1_pos A.hswitch21_pos hgap2_nonneg
      hswitch21_lt_Q2 A.acceptAll_lower_left_nonpos
  exact
    theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_fixed_lower_cross_no_rmax_normalized_mass
      μ arrival rho R1 R2 switch12 switch21
      { hR1_eq := A.hR1_eq
        hR2_pos := A.hR2_pos
        hC_lt_rho := A.hC_lt_rho
        hrho_lt_one := A.hrho_lt_one
        harrival1_pos := A.harrival1_pos
        harrival2_pos := A.harrival2_pos
        hswitch12_pos := A.hswitch12_pos
        hswitch21_pos := A.hswitch21_pos
        htime1_integrable := A.htime1_integrable
        htime2_integrable := A.htime2_integrable
        hq1_integrable := A.hq1_integrable
        hq2_integrable := A.hq2_integrable
        hmass1_eq_one := A.hmass1_eq_one
        hmass2_eq_one := A.hmass2_eq_one
        acceptAll_lower_nonpos := haccept_lower_nonpos
        arrival_nonsurge_ratio_numerator_bound :=
          A.arrival_nonsurge_ratio_numerator_bound
        current_fixed_lower_cross := A.current_fixed_lower_cross }

/--
If the moving-state accept-all gap is at most its raw switch rate, then every
positive fixed-state primitive has a strictly negative Lemma 9 lower
numerator.
-/
theorem lemma9StructuredLowerNumerator_neg_of_gap_le_switch
    (T1 Q1 T2 Q2 switch21 : ℝ)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hgap_le_switch : switch21 * T2 - Q2 ≤ switch21) :
    lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 < 0 := by
  have hTgap_le :
      T1 * (switch21 * T2 - Q2) ≤ T1 * switch21 :=
    mul_le_mul_of_nonneg_left hgap_le_switch hT1_nonneg
  unfold lemma9StructuredLowerNumerator
  linarith

/--
The corresponding Lemma 9 lower endpoint is strictly negative under the
standard positive-denominator primitive signs.  This is the policy-uniform
scalar step needed to choose one surge price rather than a new ratio for each
current non-surge policy.
-/
theorem lemma9StructuredLower_neg_of_gap_le_switch
    (T1 Q1 T2 Q2 switch21 : ℝ)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch21_pos : 0 < switch21)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hgap_le_switch : switch21 * T2 - Q2 ≤ switch21) :
    lemma9StructuredLower T1 Q1 T2 Q2 switch21 < 0 := by
  have hnum_neg :=
    lemma9StructuredLowerNumerator_neg_of_gap_le_switch
      T1 Q1 T2 Q2 switch21 hT1_nonneg hQ1_pos hgap_le_switch
  have hB_pos : 0 < Q1 + T1 * switch21 := by
    exact add_pos_of_pos_of_nonneg hQ1_pos
      (mul_nonneg hT1_nonneg (le_of_lt hswitch21_pos))
  have hden_pos :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21 := by
    unfold lemma9StructuredLowerDenominator
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt hQ1_pos) hgap_nonneg)
      (mul_pos hswitch21_pos hB_pos)
  unfold lemma9StructuredLower
  exact div_neg_of_neg_of_pos hnum_neg hden_pos

/--
Source-shaped Theorem 3 assumptions for the verified small-surge-gap subcase.
Unlike the older reward-rate-data interface, this package contains no
policy-dependent reward-rate equation or Lemma 9 conclusion.  The final field
is a primitive accept-all CTMC gap bound; Lean derives the required Lemma 9
lower inequality uniformly for every feasible positive-mass policy.

The unrestricted source theorem still requires a proof that one fixed surge
intercept lies in all policy-dependent Lemma 9 intervals.  Per-policy interval
nonemptiness alone does not discharge that uniform-intersection obligation.
-/
structure Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeGapDataAssumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) where
  hR1_eq : R1 = rho * R2
  hR2_pos : 0 < R2
  hC_lt_rho :
    theorem3FeasibilityThresholdC
        (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
        (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
        (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
        (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
        switch12 < rho
  hrho_lt_one : rho < 1
  harrival1_pos : 0 < arrival 0
  harrival2_pos : 0 < arrival 1
  hswitch12_pos : 0 < switch12
  hswitch21_pos : 0 < switch21
  htime1_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0)
  htime2_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1)
  hq1_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
      acceptAllPolicy (μ 0)
  hq2_integrable :
    IntegrableOn
      (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
      acceptAllPolicy (μ 1)
  hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1
  hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1
  arrival_nonsurge_ratio_numerator_bound :
    (arrival 0) *
        (rho * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) -
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1)) ≤
      gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
        switch12
  surge_acceptAll_gap_le_switch :
    switch21 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) -
        gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 ≤
      switch21

/--
The paper's ratio condition does not, by scalar algebra alone, imply the
nonsurge reward-envelope inequality used by the verified mass-affine route.
This checked counterexample prevents that independent obligation from being
silently reconstructed as a consequence of `C < rho`.
-/
theorem theorem3_ratio_condition_does_not_imply_arrival_nonsurge_envelope :
    theorem3FeasibilityThresholdC
        (2 : ℝ) 2 ((3 : ℝ) / 2) ((3 : ℝ) / 2) 1 < (3 : ℝ) / 4 ∧
      ¬ ((2 : ℝ) *
          (((3 : ℝ) / 4) * 2 - (2 - 1)) ≤
        (3 : ℝ) / 2 - 1) := by
  norm_num [theorem3FeasibilityThresholdC, theorem3FeasibilityNumerator,
    theorem3FeasibilityDenominator]

/--
The per-policy feasibility calculation in source Lemma 9 does not by itself
produce one ratio usable for every fixed non-surge policy.  Here both scalar
intervals are nonempty, while their intersection is empty.  The example also
satisfies the Theorem 3 displayed `C < R1 / R2 < 1` scalar condition, so that
condition cannot justify the source proof's quantifier exchange.

This is an audit counterexample to the inference from
`forall policy, exists ratio` to `exists ratio, forall policy`; it is not a
counterexample to the paper's full CTMC price-existence statement.
-/
theorem theorem3_per_policy_lemma9_intervals_do_not_yield_uniform_ratio :
    theorem3FeasibilityThresholdC (20 : ℝ) 10 2 2 1 < (19 : ℝ) / 20 ∧
      (19 : ℝ) / 20 < 1 ∧
      (∃ ratio : ℝ, lemma9StructuredBounds ratio 1 1 10 2 1) ∧
      (∃ ratio : ℝ, lemma9StructuredBounds ratio 20 2 10 2 1) ∧
      ¬ ∃ ratio : ℝ,
        lemma9StructuredBounds ratio 1 1 10 2 1 ∧
          lemma9StructuredBounds ratio 20 2 10 2 1 := by
  constructor
  · norm_num [theorem3FeasibilityThresholdC, theorem3FeasibilityNumerator,
      theorem3FeasibilityDenominator]
  constructor
  · norm_num
  constructor
  · refine ⟨1, ?_⟩
    norm_num [lemma9StructuredBounds, lemma9StructuredLower,
      lemma9StructuredLowerNumerator, lemma9StructuredLowerDenominator,
      lemma9StructuredUpper, lemma9StructuredUpperNumerator,
      lemma9StructuredUpperDenominator]
  constructor
  · refine ⟨4, ?_⟩
    norm_num [lemma9StructuredBounds, lemma9StructuredLower,
      lemma9StructuredLowerNumerator, lemma9StructuredLowerDenominator,
      lemma9StructuredUpper, lemma9StructuredUpperNumerator,
      lemma9StructuredUpperDenominator]
  rintro ⟨ratio, hsmall, hlarge⟩
  norm_num [lemma9StructuredBounds, lemma9StructuredLower,
    lemma9StructuredLowerNumerator, lemma9StructuredLowerDenominator,
    lemma9StructuredUpper, lemma9StructuredUpperNumerator,
    lemma9StructuredUpperDenominator] at hsmall hlarge
  linarith

/--
Theorem 3 on the explicit small-surge-gap domain.  The construction derives
the current-policy Lemma 9 lower bound from measured CTMC primitives and then
uses the verified policy-uniform upper slack route to construct one structured
price pair that is measurable incentive compatible on the positive-mass
source domain.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_gap
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeGapDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  let z0 :=
    theorem3NonsurgeZRatio rho
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      switch12 * R2
  let Rmax := if z0 ≤ 0 then R2 else max R2 ((arrival 0) * z0)
  have hmass1_pos : 0 < singleStateTripMass (μ 0) acceptAllPolicy := by
    rw [A.hmass1_eq_one]
    norm_num
  have hmass2_pos : 0 < singleStateTripMass (μ 1) acceptAllPolicy := by
    rw [A.hmass2_eq_one]
    norm_num
  have hmeasure1_pos : 0 < (μ 0) acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_pos
      (μ 0) acceptAllPolicy hmass1_pos
  have hmeasure2_pos : 0 < (μ 1) acceptAllPolicy :=
    measure_pos_of_singleStateTripMass_pos
      (μ 1) acceptAllPolicy hmass2_pos
  rcases theorem3_acceptAll_ratio_source_scalar_consequences
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      rho R1 R2 A.hR1_eq A.hR2_pos A.hC_lt_rho A.hrho_lt_one
      A.harrival1_pos A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
      A.htime1_integrable A.hq1_integrable hmeasure1_pos with
    ⟨_, hR1_pos, hR1_lt_R2⟩
  rcases theorem3_acceptAll_measured_primitives_scalar_conditions_positive_primitives
      μ arrival switch12 switch21 A.harrival1_pos A.harrival2_pos
      A.hswitch12_pos A.hswitch21_pos A.htime1_integrable
      A.htime2_integrable A.hq1_integrable A.hq2_integrable
      hmeasure1_pos hmeasure2_pos with
    ⟨_, _, _, _, _, _, hswitch21_lt_Q2⟩
  have hsum12 : 0 < switch12 + switch21 := by
    linarith [A.hswitch12_pos, A.hswitch21_pos]
  have hRmax_envelope :
      (z0 ≤ 0 ∧ Rmax = R2) ∨
        (0 ≤ z0 ∧ Rmax = max R2 ((arrival 0) * z0)) := by
    by_cases hz0_nonpos : z0 ≤ 0
    · left
      exact ⟨hz0_nonpos, by simp [Rmax, hz0_nonpos]⟩
    · right
      have hz0_nonneg : 0 ≤ z0 := le_of_lt (lt_of_not_ge hz0_nonpos)
      exact ⟨hz0_nonneg, by simp [Rmax, hz0_nonpos]⟩
  have hfinite1_acceptAll : (μ 0) acceptAllPolicy ≠ ⊤ :=
    singleStateTripMass_ne_top_of_eq_one A.hmass1_eq_one
  exact
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_lower_final_sign_arrival_bound_data_assumptions
      μ arrival rho R1 R2 switch12 switch21
      { Rmax := Rmax
        hR1_eq := A.hR1_eq
        hR1_pos := hR1_pos
        hR1_lt_R2 := hR1_lt_R2
        hR2_pos := A.hR2_pos
        hC_lt_rho := A.hC_lt_rho
        hrho_lt_one := A.hrho_lt_one
        harrival1_pos := A.harrival1_pos
        harrival2_pos := A.harrival2_pos
        hswitch12_pos := A.hswitch12_pos
        hswitch21_pos := A.hswitch21_pos
        htime1_integrable := A.htime1_integrable
        htime2_integrable := A.htime2_integrable
        hq1_integrable := A.hq1_integrable
        hq2_integrable := A.hq2_integrable
        hmass1_pos := hmass1_pos
        hmass2_pos := hmass2_pos
        hmass1_eq_one := A.hmass1_eq_one
        hfinite1_acceptAll := hfinite1_acceptAll
        Rmax_envelope := by simpa [z0] using hRmax_envelope
        arrival_nonsurge_ratio_numerator_bound :=
          A.arrival_nonsurge_ratio_numerator_bound
        current_lower_left_nonpos := by
          intro policy hpolicy
          have hQcurrent_pos :
              0 < gn21ExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21 (policy 0) :=
            gn21ExitWeightIntegral_pos_of_switch_pos
              (μ 0) (arrival 0) switch12 switch21 (policy 0)
              (le_of_lt A.harrival1_pos) A.hswitch12_pos hsum12
              (hpolicy.1 0).2 (hpolicy.1 0).1
          have hnum_neg :=
            lemma9StructuredLowerNumerator_neg_of_gap_le_switch
              (gn21ScaledStateTime (μ 0) (arrival 0) (policy 0))
              (gn21ExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21 (policy 0))
              (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
              (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                switch21 switch12)
              switch21
              (le_of_lt <|
                gn21ScaledStateTime_pos_of_nonneg
                  (μ 0) (arrival 0) (policy 0)
                  (le_of_lt A.harrival1_pos) (hpolicy.1 0).2
                  (hpolicy.1 0).1)
              hQcurrent_pos
              A.surge_acceptAll_gap_le_switch
          have hupper_den_pos :
              0 < lemma9StructuredUpperDenominator
                (gn21ExitWeightIntegral (μ 0) (arrival 0)
                  switch12 switch21 (policy 0))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                  switch21 switch12)
                switch21 := by
            unfold lemma9StructuredUpperDenominator
            exact mul_pos hQcurrent_pos (sub_pos.mpr hswitch21_lt_Q2)
          exact le_of_lt (mul_neg_of_neg_of_pos hnum_neg hupper_den_pos) }

/--
Theorem 3 positive-mass measurable IC on the source-shaped small-surge route.
The remaining policy-dependent input is the current Lemma 9 lower final-sign
condition; Lean derives the accept-all lower endpoint and the uniform upper
slack internally.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_final_sign
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackFinalSignDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
      μ arrival rho R1 R2 switch12 switch21 A

/--
Preferred Theorem 3 frontier when the current Lemma 9 lower endpoint may be
positive.  The source supplies exact selected-price lower interval slack, while
Lean keeps the small-surge upper slack and accept-all sequencing internal.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_interval_final_sign
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeCurrentIntervalSlackFinalSignDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
      μ arrival rho R1 R2 switch12 switch21 A

/--
Mass-affine Theorem 3 frontier with selected-price lower interval slack.  This
keeps the paper proof on the small-surge route while using the tighter
mass-affine non-surge reward envelope.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_interval_final_sign
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineCurrentIntervalSlackFinalSignDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 :=
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_data_assumptions
      μ arrival rho R1 R2 switch12 switch21 A

end

end GN21DriverSurgePricing
