import GN21DriverSurgePricing.MainTheorems

/-!
# Lemma 5 Frontier Routes for Driver Surge Pricing

This file holds active Lemma 5 proof-route adapters that build on the stable
GN21 continuous proof base in `MainTheorems.lean`.  Keeping these frontier
constructors here lets future proof work target this module instead of
rechecking the full theorem ledger after every small route edit.
-/

open AppliedModelingLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/-!
## Source-style Lemma 5 replacement shortcuts

These helpers cover exact current-policy branches that the paper proof reaches
after Lemma 5.  They avoid rebuilding a replacement certificate when the
current feasible policy already has the canonical middle-interval form.
-/

/--
If the current feasible non-surge policy already has exact middle-acceptance
syntax, the Lemma 5 replacement can be the current policy itself.
-/
def Theorem4NonsurgeAllowedReplacementData.of_acceptsMiddle_current
    {Rhat : SingleStateReward} {σ0 : TripPolicy} {lo hi : ℝ}
    (hσ0_subset : σ0 ⊆ acceptAllPolicy)
    (hshape : acceptsMiddleTrips lo hi σ0) :
    Theorem4NonsurgeAllowedReplacementData Rhat σ0 :=
  .acceptMiddle lo hi
    (by
      have hpolicy_eq :
          σ0 = acceptMiddleTripsPolicy lo hi :=
        eq_acceptMiddleTripsPolicy_of_acceptsMiddleTrips_of_subset_acceptAll
          hshape hσ0_subset
      simp [hpolicy_eq])
    (by
      intro hnot
      have hpolicy_eq :
          σ0 = acceptMiddleTripsPolicy lo hi :=
        eq_acceptMiddleTripsPolicy_of_acceptsMiddleTrips_of_subset_acceptAll
          hshape hσ0_subset
      have hform : lemma5PolicyForm .strictlyQuasiConcave σ0 := by
        rw [hpolicy_eq]
        exact lemma5PolicyForm_strictlyQuasiConcave_acceptMiddleTripsPolicy lo hi
      exact False.elim (hnot hform))

/--
If the current feasible surge policy already has exact middle-rejection syntax,
the Lemma 5 replacement can be the current policy itself.
-/
def Theorem4SurgeAllowedReplacementData.of_rejectsMiddle_current
    {Rhat : SingleStateReward} {σ0 : TripPolicy} {lo hi : ℝ}
    (hσ0_subset : σ0 ⊆ acceptAllPolicy)
    (hshape : rejectsMiddleTrips lo hi σ0) :
    Theorem4SurgeAllowedReplacementData Rhat σ0 :=
  .rejectMiddle lo hi
    (by
      have hpolicy_eq :
          σ0 = rejectMiddleTripsPolicy lo hi :=
        eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
          hshape hσ0_subset
      simp [hpolicy_eq])
    (by
      intro hnot
      have hpolicy_eq :
          σ0 = rejectMiddleTripsPolicy lo hi :=
        eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
          hshape hσ0_subset
      have hform : lemma5PolicyForm .strictlyQuasiConvex σ0 := by
        rw [hpolicy_eq]
        exact lemma5PolicyForm_strictlyQuasiConvex_rejectMiddleTripsPolicy lo hi
      exact False.elim (hnot hform))

/-!
## Theorem 4 structural endpoints from Lemma 5 frontier data

The source Theorem 4 statement is existential: there is an optimal dynamic
policy with the listed statewise forms, and every optimal policy has one of
those forms.  The core theorem ledger already proves the shape-derivation
route.  These frontier endpoints let the paper-facing surface consume the
lighter allowed-form and feasible canonical-dominance Lemma 5 boundaries
directly.
-/

/--
Allowed Lemma 5 policy forms for every measurable optimum imply the paper's
measurable Theorem 4 structural statement: an optimal policy with the listed
statewise forms exists, and every measurable optimum has the listed forms.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_of_allowed_policy_forms
    (R : DynamicReward)
    (C : Theorem4AllMeasurableAllowedPolicyFormsCertificate R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        theorem4NonsurgeShape (ρstar 0) ∧
        theorem4SurgeShape (ρstar 1) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) := by
  rcases C.exists_optimal with ⟨ρstar, hρstar⟩
  rcases C.only_policy_forms ρstar hρstar with
    ⟨⟨nshape, hnallowed, hnform⟩, ⟨sshape, hsallowed, hsform⟩⟩
  refine ⟨ρstar, hρstar, ?_, ?_, ?_⟩
  · exact theorem4NonsurgeShape_of_allowed_lemma5_form hnallowed hnform
  · exact theorem4SurgeShape_of_allowed_lemma5_form hsallowed hsform
  · intro ρ hρ
    rcases C.only_policy_forms ρ hρ with
      ⟨⟨nshape, hnallowed, hnform⟩, ⟨sshape, hsallowed, hsform⟩⟩
    exact
      ⟨theorem4NonsurgeShape_of_allowed_lemma5_form hnallowed hnform,
        theorem4SurgeShape_of_allowed_lemma5_form hsallowed hsform⟩

/--
Source-style Lemma 5 replacement data for every measurable optimum imply the
paper's measurable Theorem 4 structural statement.  This is closer to the
paper proof than prepackaged policy-form data: Lean first turns the feasible
replacement certificates into allowed policy forms using optimality.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_of_allowed_replacement_data
    (R : DynamicReward)
    (D : Theorem4AllMeasurableOptimalAllowedReplacementData R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        theorem4NonsurgeShape (ρstar 0) ∧
        theorem4SurgeShape (ρstar 1) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) :=
  paper_theorem4_measurable_dynamic_structural_policy_of_allowed_policy_forms
    R
    (Theorem4AllMeasurableAllowedPolicyFormsCertificate.of_shape_replacements
      D.to_shape_replacements)

/--
Feasible policy-level canonical-dominance Lemma 5 data imply the paper's
measurable Theorem 4 structural endpoint.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_of_feasible_policy_canonical_dominance
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D : Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        theorem4NonsurgeShape (ρstar 0) ∧
        theorem4SurgeShape (ρstar 1) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) :=
  paper_theorem4_measurable_dynamic_structural_policy_of_allowed_policy_forms
    R (D.to_allowed_policy_forms)

/--
Feasible a.e. Lemma 5 policy-form representatives imply the paper's
measure-theoretic Theorem 4 statement: an optimal policy has non-surge and
surge representatives of the listed forms, and every measurable optimum has
such representatives.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_ae_policy_forms
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    (D : Theorem4AllMeasurableFeasibleAEPolicyFormData μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) := by
  rcases D.exists_optimal with ⟨ρstar, hρstar⟩
  have hnstar :
      ∃ σstar : TripPolicy,
        theorem4NonsurgeShape σstar ∧
          policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar := by
    rcases D.nonsurge ρstar hρstar with ⟨nshape, ndata⟩
    exact
      theorem4NonsurgeShapeRepresentative_of_allowed_lemma5_formAE
        (μ 0) nshape.2 ndata.to_policyFormAlmostEverywhere
  have hsstar :
      ∃ σstar : TripPolicy,
        theorem4SurgeShape σstar ∧
          policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar := by
    rcases D.surge ρstar hρstar with ⟨sshape, sdata⟩
    exact
      theorem4SurgeShapeRepresentative_of_allowed_lemma5_formAE
        (μ 1) sshape.2 sdata.to_policyFormAlmostEverywhere
  refine ⟨ρstar, hρstar, hnstar, hsstar, ?_⟩
  intro ρ hρ
  constructor
  · rcases D.nonsurge ρ hρ with ⟨nshape, ndata⟩
    exact
      theorem4NonsurgeShapeRepresentative_of_allowed_lemma5_formAE
        (μ 0) nshape.2 ndata.to_policyFormAlmostEverywhere
  · rcases D.surge ρ hρ with ⟨sshape, sdata⟩
    exact
      theorem4SurgeShapeRepresentative_of_allowed_lemma5_formAE
        (μ 1) sshape.2 sdata.to_policyFormAlmostEverywhere

/--
Allowed exact policy forms imply the same a.e.-representative Theorem 4
surface.  This is useful when a proof already closed exact Lemma 5 forms but
the human-facing paper statement should keep the source's null-set wording.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_allowed_policy_forms
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    (C : Theorem4AllMeasurableAllowedPolicyFormsCertificate R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_ae_policy_forms
    μ R (C.to_feasible_ae_policy_forms)

/--
Source-style Lemma 5 replacement data also imply the a.e.-representative
version of Theorem 4.  This is the paper-facing null-set statement to use when
the source proof constructs canonical replacements rather than exact policy
forms.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_allowed_replacement_data
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    (D : Theorem4AllMeasurableOptimalAllowedReplacementData R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_allowed_policy_forms
    μ R
    (Theorem4AllMeasurableAllowedPolicyFormsCertificate.of_shape_replacements
      D.to_shape_replacements)

/--
Feasible policy-level canonical-dominance Lemma 5 data imply the source
Theorem 4 structural statement with explicit a.e. representatives.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_policy_canonical_dominance
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D : Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_allowed_policy_forms
    μ R (D.to_allowed_policy_forms)

/--
Fixed-response analytic Lemma 5 shape data imply the source Theorem 4
structural statement with explicit a.e. representatives.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_fixed_response_shape_data
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (D : Theorem4AllMeasurableFixedResponseShapeData μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_ae_policy_forms
    μ R (D.to_feasible_ae_policy_forms)

/--
Fixed-response policy-form Lemma 5 data imply the source Theorem 4 structural
statement with explicit a.e. representatives.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_fixed_response_policy_forms
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (D : Theorem4AllMeasurableFixedResponsePolicyFormData μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_ae_policy_forms
    μ R (D.to_feasible_ae_policy_forms)

/--
GN21 fixed-response source records imply the source Theorem 4 a.e.
structural-representative statement for the measured dynamic reward.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_fixed_response_source_data
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (D :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormSourceData μ arrival
        switch12 switch21 w) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_fixed_response_policy_forms
    μ (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
    (D.to_fixed_response_policy_form_data)

/--
Raw GN21 Lemma 6 bracket records imply the source Theorem 4 a.e.
structural-representative statement for one-threshold CTMC prices.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_bracket_source_data
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (D :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_fixed_response_policy_forms
    μ
    (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
    (D.to_fixed_response_policy_form_data)

/--
The raw GN21 Lemma 6 bracket package also gives the Theorem 2 policy-shape
part for one-threshold CTMC prices: every measurable optimum rejects long
non-surge trips and short surge trips, up to null feasible-trip sets.
-/
theorem paper_theorem2_one_threshold_measurable_policy_shape_ae_of_gn21_bracket_source_data
    (μ : Fin 2 → Measure TripLength)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (D :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z) :
    (∃ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ ∧
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (μ 0) (ρ 0) ∧
        rejectsShortTripsAlmostEverywhere (μ 1) (ρ 1)) ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (μ 0) (ρ 0) ∧
          rejectsShortTripsAlmostEverywhere (μ 1) (ρ 1) := by
  let R :=
    gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
  refine
    paper_theorem2_multiplicative_measurable_policy_shape_ae_of_certificate
      μ R ?_
  refine
    { exists_optimal := D.exists_optimal
      nonsurge := ?_
      surge := ?_ }
  · intro ρ hρ
    let N :=
      (D.nonsurge ρ hρ).to_source_data D.hswitch12_pos
        (add_pos D.hswitch12_pos D.hswitch21_pos)
    let F := N.to_fixed_response hρ
    exact
      { shape := .strictlyDecreasing
        branch := Or.inr rfl
        form :=
          F.to_feasiblePolicyFormAlmostEverywhere
            (hρ.1 0).2 (hρ.1 0).1 }
  · intro ρ hρ
    let S :=
      (D.surge ρ hρ).to_source_data D.hswitch21_pos
        (add_pos D.hswitch21_pos D.hswitch12_pos)
    let F := S.to_fixed_response hρ
    exact
      { shape := .strictlyIncreasing
        branch := Or.inr rfl
        form :=
          F.to_feasiblePolicyFormAlmostEverywhere
            (hρ.1 1).2 (hρ.1 1).1 }

/--
Accept-all optimality plus a.e. accept-all uniqueness gives the Theorem 4
accept-all structural representative statement.
-/
theorem paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_acceptAll_ae_unique
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    (H :
      dynamicMeasurableOptimal R acceptAllDynamicPolicy ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal R ρ →
            dynamicAcceptAllAlmostEverywhere μ ρ) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) := by
  refine
    ⟨acceptAllDynamicPolicy, H.1,
      ⟨acceptAllPolicy, theorem4NonsurgeShape_acceptAllPolicy, ?_⟩,
      ⟨acceptAllPolicy, theorem4SurgeShape_acceptAllPolicy, ?_⟩,
      ?_⟩
  · simp [acceptAllDynamicPolicy, policyAlmostEverywhereEq]
  · simp [acceptAllDynamicPolicy, policyAlmostEverywhereEq]
  · intro ρ hρ
    have hae := H.2 ρ hρ
    constructor
    · refine ⟨acceptAllPolicy, theorem4NonsurgeShape_acceptAllPolicy, ?_⟩
      exact
        policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
          (μ 0) (hρ.1 0).1 (hae 0)
    · refine ⟨acceptAllPolicy, theorem4SurgeShape_acceptAllPolicy, ?_⟩
      exact
        policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
          (μ 1) (hρ.1 1).1 (hae 1)

/--
Positive-response marginal optimality gives the Theorem 4 structural
representative statement in the accept-all branch.
-/
theorem paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_positive_response_marginal_optima
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    (C : Theorem4MeasurablePositiveResponseAEMarginalCertificate μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) := by
  have H :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima
      μ R C
  refine
    ⟨acceptAllDynamicPolicy, H.1,
      ⟨acceptAllPolicy, theorem4NonsurgeShape_acceptAllPolicy, ?_⟩,
      ⟨acceptAllPolicy, theorem4SurgeShape_acceptAllPolicy, ?_⟩,
      ?_⟩
  · simp [acceptAllDynamicPolicy, policyAlmostEverywhereEq]
  · simp [acceptAllDynamicPolicy, policyAlmostEverywhereEq]
  · intro ρ hρ
    have hae := H.2 ρ hρ
    constructor
    · refine ⟨acceptAllPolicy, theorem4NonsurgeShape_acceptAllPolicy, ?_⟩
      exact
        policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
          (μ 0) (hρ.1 0).1 (hae 0)
    · refine ⟨acceptAllPolicy, theorem4SurgeShape_acceptAllPolicy, ?_⟩
      exact
        policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
          (μ 1) (hρ.1 1).1 (hae 1)

/--
The weaker accept-all-candidate positive-response certificate also gives the
Theorem 4 structural representative statement in the accept-all branch.
-/
theorem paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    (C : Theorem4MeasurablePositiveResponseAEAcceptAllCandidateCertificate μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) := by
  have H :=
    paper_theorem4_measurable_accept_all_ae_unique_optimal_of_positive_response_acceptAll_candidates
      μ R C
  refine
    ⟨acceptAllDynamicPolicy, H.1,
      ⟨acceptAllPolicy, theorem4NonsurgeShape_acceptAllPolicy, ?_⟩,
      ⟨acceptAllPolicy, theorem4SurgeShape_acceptAllPolicy, ?_⟩,
      ?_⟩
  · simp [acceptAllDynamicPolicy, policyAlmostEverywhereEq]
  · simp [acceptAllDynamicPolicy, policyAlmostEverywhereEq]
  · intro ρ hρ
    have hae := H.2 ρ hρ
    constructor
    · refine ⟨acceptAllPolicy, theorem4NonsurgeShape_acceptAllPolicy, ?_⟩
      exact
        policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
          (μ 0) (hρ.1 0).1 (hae 0)
    · refine ⟨acceptAllPolicy, theorem4SurgeShape_acceptAllPolicy, ?_⟩
      exact
        policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
          (μ 1) (hρ.1 1).1 (hae 1)

/--
Optimal-policy current-bounds source data give the paper-facing Theorem 4
accept-all structural representative statement through the candidate-only
positive-response route.
-/
theorem paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_structured_current_bounds_optimal_source_positive_response
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ)
    (C :
      Theorem4MeasuredAggregateStructuredCurrentBoundsOptimalSourcePositiveResponseCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_positive_response_acceptAll_candidates
    μ
    (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
    (Theorem4MeasurablePositiveResponseAEAcceptAllCandidateCertificate.of_structured_current_bounds_optimal_source
      μ arrival R1 R2 switch12 switch21 m z C)

/--
Reward-rate current-bounds data give the same paper-facing Theorem 4
accept-all structural representative statement after Lean converts the local
Lemma 9/10 reward-rate fields to source data.
-/
theorem paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_structured_current_bounds_optimal_reward_rate_positive_response
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ)
    (C :
      Theorem4MeasuredAggregateStructuredCurrentBoundsOptimalRewardRatePositiveResponseCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_structured_current_bounds_optimal_source_positive_response
    μ arrival R1 R2 switch12 switch21 m z
    (Theorem4MeasuredAggregateStructuredCurrentBoundsOptimalSourcePositiveResponseCertificate.of_optimal_reward_rate
      μ arrival R1 R2 switch12 switch21 m z C)

/--
Positive-response marginal dominance transfers to any objective that is a
positive affine transform of that marginal reward on feasible measurable
policies.
-/
def Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal_positive_affine
    {Rhat : SingleStateReward}
    (μ : Measure TripLength) (response : TripLength → ℝ)
    (σ0 : TripPolicy) (shape : Lemma5DerivativeShape)
    (hσ0_open : IsOpen σ0)
    (hσ0_subset : σ0 ⊆ acceptAllPolicy)
    (hcont : GN21SymmDiffContinuousAt μ Rhat σ0)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy μ)
    (hpositive_form :
      lemma5PolicyForm shape (lemma5PositiveResponsePolicy response))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape σ0 →
        0 < μ (lemma5PositiveResponsePolicy response \ σ0) ∨
        0 <
          μ (Function.support response ∩
            (σ0 \ lemma5PositiveResponsePolicy response)))
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ = scale * lemma5MarginalSetReward μ response σ + offset) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      μ Rhat σ0 shape where
  hσ0_open := hσ0_open
  hσ0_subset := hσ0_subset
  hcont := hcont
  canonicalPolicyMax := by
    let P : TripPolicy := lemma5PositiveResponsePolicy response
    have hP_subset : P ⊆ acceptAllPolicy :=
      lemma5PositiveResponsePolicy_subset_acceptAll response
    have hP_measurable : MeasurableSet P :=
      measurableSet_lemma5PositiveResponsePolicy response
        hresponse_measurable
    refine ⟨P, hP_subset, hP_measurable, hpositive_form, ?_⟩
    intro seed hseed_form
    have hmarg :
        lemma5MarginalSetReward μ response seed.policy ≤
          lemma5MarginalSetReward μ response P :=
              lemma5MarginalSetReward_le_positiveResponsePolicy
          μ response seed.policy hresponse_measurable
          hresponse_integrable_acceptAll seed.measurableSet_policy
          seed.subset_acceptAll
    have hseed_aff :=
      haffine seed.policy seed.subset_acceptAll seed.measurableSet_policy
    have hP_aff := haffine P hP_subset hP_measurable
    rw [hseed_aff, hP_aff]
    nlinarith [hscale_pos, hmarg]
  policyCanonicalDominance := by
    intro seed hnot
    let P : TripPolicy := lemma5PositiveResponsePolicy response
    have hP_subset : P ⊆ acceptAllPolicy :=
      lemma5PositiveResponsePolicy_subset_acceptAll response
    have hP_measurable : MeasurableSet P :=
      measurableSet_lemma5PositiveResponsePolicy response
        hresponse_measurable
    refine ⟨P, hP_subset, hpositive_form, ?_⟩
    have hmarg :
        lemma5MarginalSetReward μ response seed.policy ≤
          lemma5MarginalSetReward μ response P :=
              lemma5MarginalSetReward_le_positiveResponsePolicy
          μ response seed.policy hresponse_measurable
          hresponse_integrable_acceptAll seed.measurableSet_policy
          seed.subset_acceptAll
    have hseed_aff :=
      haffine seed.policy seed.subset_acceptAll seed.measurableSet_policy
    have hP_aff := haffine P hP_subset hP_measurable
    rw [hseed_aff, hP_aff]
    nlinarith [hscale_pos, hmarg]
  policyStrictWitness := by
    intro hnot
    let P : TripPolicy := lemma5PositiveResponsePolicy response
    have hP_subset : P ⊆ acceptAllPolicy :=
      lemma5PositiveResponsePolicy_subset_acceptAll response
    have hP_measurable : MeasurableSet P :=
      measurableSet_lemma5PositiveResponsePolicy response
        hresponse_measurable
    refine ⟨P, hP_subset, hpositive_form, ?_⟩
    have hmarg :
        lemma5MarginalSetReward μ response σ0 <
          lemma5MarginalSetReward μ response P := by
      rcases hstrict_mass hnot with homitted | hnegative
      · exact
          lemma5MarginalSetReward_lt_positiveResponsePolicy_of_omits_positive_mass
            μ response σ0 hresponse_measurable hresponse_integrable_acceptAll
            hσ0_open.measurableSet hσ0_subset homitted
      · exact
          lemma5MarginalSetReward_lt_positiveResponsePolicy_of_accepts_negative_mass
            μ response σ0 hresponse_measurable hresponse_integrable_acceptAll
            hσ0_open.measurableSet hσ0_subset hnegative
    have hσ0_aff := haffine σ0 hσ0_subset hσ0_open.measurableSet
    have hP_aff := haffine P hP_subset hP_measurable
    rw [hσ0_aff, hP_aff]
    nlinarith [hscale_pos, hmarg]

/--
Positive-affine objective changes preserve the source-faithful a.e. Lemma 5
policy-form conclusion.  This is weaker than the exact canonical-dominance
constructor above: it only needs the current policy to beat the canonical
positive-response policy in the transformed objective, and then delegates the
null-boundary work to the existing a.e. Lemma 5 theorem.
-/
def Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_positive_affine_candidate_le
    {Rhat : SingleStateReward}
    (μ : Measure TripLength) [NoAtoms μ]
    {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
    (D : Lemma5PositiveResponsePolicyFormData response shape)
    (σ : TripPolicy)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy μ)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ acceptAllPolicy)
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ' : TripPolicy,
        σ' ⊆ acceptAllPolicy →
        MeasurableSet σ' →
          Rhat σ' = scale * lemma5MarginalSetReward μ response σ' + offset)
    (hcandidate :
      Rhat (lemma5PositiveResponsePolicy response) ≤ Rhat σ) :
    Lemma5FeasiblePolicyFormAlmostEverywhereData μ shape σ := by
  let P : TripPolicy := lemma5PositiveResponsePolicy response
  have hP_subset : P ⊆ acceptAllPolicy :=
    lemma5PositiveResponsePolicy_subset_acceptAll response
  have hP_measurable : MeasurableSet P :=
    measurableSet_lemma5PositiveResponsePolicy response hresponse_measurable
  have hP_aff := haffine P hP_subset hP_measurable
  have hσ_aff := haffine σ hσ_subset hσ_measurable
  have hmarg_candidate :
      lemma5MarginalSetReward μ response P ≤
        lemma5MarginalSetReward μ response σ := by
    rw [hP_aff, hσ_aff] at hcandidate
    nlinarith [hscale_pos, hcandidate]
  exact
    D.feasiblePolicyFormAlmostEverywhere_of_candidate_le
      μ σ hresponse_measurable hresponse_integrable_acceptAll
      hσ_measurable hσ_subset (by simpa [P] using hmarg_candidate)

/--
Feasible optimality for a positive-affine transform of the Lemma 5 marginal
reward gives the a.e. canonical policy-form representative directly.  Use this
when the paper proof has local optimality for a transformed continuation
objective rather than for the raw marginal set reward.
-/
def Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_positive_affine_feasible_optimal
    {Rhat : SingleStateReward}
    (μ : Measure TripLength) [NoAtoms μ]
    {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
    (D : Lemma5PositiveResponsePolicyFormData response shape)
    (σ : TripPolicy)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy μ)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ acceptAllPolicy)
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ' : TripPolicy,
        σ' ⊆ acceptAllPolicy →
        MeasurableSet σ' →
          Rhat σ' = scale * lemma5MarginalSetReward μ response σ' + offset)
    (hoptimal :
      ∀ σ' : TripPolicy,
        σ' ⊆ acceptAllPolicy →
        MeasurableSet σ' →
          Rhat σ' ≤ Rhat σ) :
    Lemma5FeasiblePolicyFormAlmostEverywhereData μ shape σ :=
  D.feasiblePolicyFormAlmostEverywhere_of_positive_affine_candidate_le
    μ σ hresponse_measurable hresponse_integrable_acceptAll
    hσ_measurable hσ_subset scale offset hscale_pos haffine
    (hoptimal (lemma5PositiveResponsePolicy response)
      (lemma5PositiveResponsePolicy_subset_acceptAll response)
      (measurableSet_lemma5PositiveResponsePolicy response
        hresponse_measurable))

/--
Dynamic local optimality plus a positive-affine fixed-state continuation
identity gives the source-faithful a.e. Lemma 5 policy-form representative.
This is the direct version of the paper's Theorem 4 "freeze the other state
and apply Lemma 5" step.
-/
def Lemma5PositiveResponsePolicyFormData.feasiblePolicyFormAlmostEverywhere_of_dynamicStateReward_positive_affine
    (R : DynamicReward)
    {ρ : Fin 2 → TripPolicy}
    (hρ : dynamicMeasurableOptimal R ρ)
    (i : Fin 2)
    (μ : Measure TripLength) [NoAtoms μ]
    {response : TripLength → ℝ} {shape : Lemma5DerivativeShape}
    (D : Lemma5PositiveResponsePolicyFormData response shape)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy μ)
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          dynamicStateReward R ρ i σ =
            scale * lemma5MarginalSetReward μ response σ + offset) :
    Lemma5FeasiblePolicyFormAlmostEverywhereData μ shape (ρ i) :=
  D.feasiblePolicyFormAlmostEverywhere_of_positive_affine_feasible_optimal
    μ (ρ i) hresponse_measurable hresponse_integrable_acceptAll
    (hρ.1 i).2 (hρ.1 i).1 scale offset hscale_pos haffine
    (by
      intro σ hσ_subset hσ_measurable
      exact
        dynamicStateReward_optimal_of_dynamicMeasurableOptimal R hρ i
          (dynamicFeasibleMeasurablePolicy_update hρ.1 i σ
            hσ_subset hσ_measurable))

/--
One fixed state of the dynamic problem has Lemma 5 policy-form data and a
positive-affine identification of its continuation reward with the marginal
set reward.  This keeps the Theorem 4 source boundary at the paper's frozen
state objective rather than requiring exact canonical-dominance data.
-/
structure Lemma5DynamicStatePositiveAffinePolicyFormData
    (R : DynamicReward)
    (ρ : Fin 2 → TripPolicy)
    (i : Fin 2)
    (μ : Measure TripLength)
    (response : TripLength → ℝ)
    (shape : Lemma5DerivativeShape) where
  marker : Unit := ()
  policy_form_data : Lemma5PositiveResponsePolicyFormData response shape
  response_measurable : Measurable response
  response_integrable_acceptAll :
    IntegrableOn response acceptAllPolicy μ
  scale : ℝ
  offset : ℝ
  scale_pos : 0 < scale
  affine :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        dynamicStateReward R ρ i σ =
          scale * lemma5MarginalSetReward μ response σ + offset

/--
Positive-affine dynamic-state policy-form data produce the a.e. Lemma 5
representative for the current state of a dynamic optimum.
-/
def Lemma5DynamicStatePositiveAffinePolicyFormData.to_feasiblePolicyFormAlmostEverywhere
    {R : DynamicReward}
    {ρ : Fin 2 → TripPolicy}
    {i : Fin 2}
    {μ : Measure TripLength} [NoAtoms μ]
    {response : TripLength → ℝ}
    {shape : Lemma5DerivativeShape}
    (D :
      Lemma5DynamicStatePositiveAffinePolicyFormData R ρ i μ response shape)
    (hρ : dynamicMeasurableOptimal R ρ) :
    Lemma5FeasiblePolicyFormAlmostEverywhereData μ shape (ρ i) :=
  D.policy_form_data.feasiblePolicyFormAlmostEverywhere_of_dynamicStateReward_positive_affine
    R hρ i μ D.response_measurable D.response_integrable_acceptAll
    D.scale D.offset D.scale_pos D.affine

/--
All measurable optima have fixed-state positive-affine policy-form data in the
Theorem 4 allowed shape families.
-/
structure Theorem4AllMeasurableDynamicStatePositiveAffinePolicyFormData
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ
  nonsurge :
    ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
      Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4NonsurgeAllowedLemma5Shape shape},
        Σ response : TripLength → ℝ,
          Lemma5DynamicStatePositiveAffinePolicyFormData
            R ρ 0 (μ 0) response shape.1
  surge :
    ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
      Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4SurgeAllowedLemma5Shape shape},
        Σ response : TripLength → ℝ,
          Lemma5DynamicStatePositiveAffinePolicyFormData
            R ρ 1 (μ 1) response shape.1

/--
Dynamic-state positive-affine policy-form data feed the feasible a.e. policy
form boundary consumed by the Theorem 4 endpoint bridge.
-/
def Theorem4AllMeasurableDynamicStatePositiveAffinePolicyFormData.to_feasible_ae_policy_forms
    {μ : Fin 2 → Measure TripLength} {R : DynamicReward}
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (C : Theorem4AllMeasurableDynamicStatePositiveAffinePolicyFormData μ R) :
    Theorem4AllMeasurableFeasibleAEPolicyFormData μ R where
  exists_optimal := C.exists_optimal
  nonsurge := by
    intro ρ hρ
    rcases C.nonsurge ρ hρ with ⟨shape, response, D⟩
    exact ⟨shape, D.to_feasiblePolicyFormAlmostEverywhere hρ⟩
  surge := by
    intro ρ hρ
    rcases C.surge ρ hρ with ⟨shape, response, D⟩
    exact ⟨shape, D.to_feasiblePolicyFormAlmostEverywhere hρ⟩

/--
The paper's frozen-state positive-affine Lemma 5 boundary implies the
measurable Theorem 4 structural statement with explicit a.e. representatives.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_dynamic_state_positive_affine_policy_forms
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward)
    [NoAtoms (μ 0)] [NoAtoms (μ 1)]
    (D : Theorem4AllMeasurableDynamicStatePositiveAffinePolicyFormData μ R) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy, dynamicMeasurableOptimal R ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_ae_policy_forms
    μ R (D.to_feasible_ae_policy_forms)

/--
Left-state measured marginal data for the feasible policy-canonical Lemma 5
route.  The canonical-dominance objective is the actual GN21 measured marginal
set reward obtained by freezing the surge-state policy.
-/
structure GN21MeasuredLeftMarginalFeasiblePolicyCanonicalDominanceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy)
    (shape : Lemma5DerivativeShape) where
  marginal_canonical_dominance :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 0)
      (lemma5MarginalSetReward (μ 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)))
      (ρ 0) shape
  arrival_pos : 0 < arrival 0
  current_nondegenerate :
    GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
      switch12 switch21 (ρ 0) (ρ 1)
  candidate_nondegenerate :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 σ (ρ 1)
  denominator_pos :
    0 <
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
          gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0)
  candidate_denominator_pos :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        0 <
          gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 σ *
              gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) *
              gn21ScaledStateTime (μ 0) (arrival 0) σ
  q_integrable :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        IntegrableOn
          (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
          σ (μ 0)
  payment_integrable :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        IntegrableOn (w 0) σ (μ 0)
  time_integrable :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (μ 0)

/--
Measured dynamic optimality turns the left-state marginal canonical-dominance
data into the exact Lemma 5 policy form for the current non-surge policy.
-/
noncomputable def GN21MeasuredLeftMarginalFeasiblePolicyCanonicalDominanceData.to_policy_form
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    (D :
      GN21MeasuredLeftMarginalFeasiblePolicyCanonicalDominanceData
        μ arrival switch12 switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ) :
    lemma5PolicyForm shape (ρ 0) := by
  have hopt :=
    lemma5MarginalSetReward_optimal_of_gn21MeasuredDynamicRewardFunctional_zero
      μ arrival switch12 switch21 w hρ D.arrival_pos
      D.current_nondegenerate D.candidate_nondegenerate D.denominator_pos
      D.candidate_denominator_pos D.q_integrable D.payment_integrable
      D.time_integrable
  exact
    D.marginal_canonical_dominance.policyForm_of_candidate_le
      (hopt D.marginal_canonical_dominance.to_optimizer_replacement.policy
        D.marginal_canonical_dominance.to_optimizer_replacement_subset
        D.marginal_canonical_dominance.to_optimizer_replacement_measurable)

/--
Right-state measured marginal data for the feasible policy-canonical Lemma 5
route.  This is the state-swapped counterpart of
`GN21MeasuredLeftMarginalFeasiblePolicyCanonicalDominanceData`.
-/
structure GN21MeasuredRightMarginalFeasiblePolicyCanonicalDominanceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy)
    (shape : Lemma5DerivativeShape) where
  marginal_canonical_dominance :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 1)
      (lemma5MarginalSetReward (μ 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)))
      (ρ 1) shape
  arrival_pos : 0 < arrival 1
  current_nondegenerate :
    GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
      switch12 switch21 (ρ 0) (ρ 1)
  candidate_nondegenerate :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) σ
  denominator_pos :
    0 <
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
          gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0)
  candidate_denominator_pos :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        0 <
          gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
              (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) σ +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 σ *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0)
  q_integrable :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        IntegrableOn
          (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
          σ (μ 1)
  payment_integrable :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        IntegrableOn (w 1) σ (μ 1)
  time_integrable :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        IntegrableOn (fun τ : TripLength => τ) σ (μ 1)

/--
Measured dynamic optimality turns the right-state marginal canonical-dominance
data into the exact Lemma 5 policy form for the current surge policy.
-/
noncomputable def GN21MeasuredRightMarginalFeasiblePolicyCanonicalDominanceData.to_policy_form
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      GN21MeasuredRightMarginalFeasiblePolicyCanonicalDominanceData
        μ arrival switch12 switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ) :
    lemma5PolicyForm shape (ρ 1) := by
  have hopt :=
    lemma5MarginalSetReward_optimal_of_gn21MeasuredDynamicRewardFunctional_one
      μ arrival switch12 switch21 w hρ D.arrival_pos
      D.current_nondegenerate D.candidate_nondegenerate D.denominator_pos
      D.candidate_denominator_pos D.q_integrable D.payment_integrable
      D.time_integrable
  exact
    D.marginal_canonical_dominance.policyForm_of_candidate_le
      (hopt D.marginal_canonical_dominance.to_optimizer_replacement.policy
        D.marginal_canonical_dominance.to_optimizer_replacement_subset
        D.marginal_canonical_dominance.to_optimizer_replacement_measurable)

/--
All-optima GN21 measured marginal canonical-dominance data.  This is the
non-positive-affine Theorem 4 route: Lean first proves each frozen-state
measured marginal objective is locally optimal, then uses the supplied Lemma 5
canonical-dominance data to classify the policy shape.
-/
structure Theorem4AllMeasurableGN21MarginalFeasiblePolicyCanonicalDominanceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ
  nonsurge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      ∃ shape :
        {shape : Lemma5DerivativeShape //
          theorem4NonsurgeAllowedLemma5Shape shape},
        GN21MeasuredLeftMarginalFeasiblePolicyCanonicalDominanceData
          μ arrival switch12 switch21 w ρ shape.1
  surge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      ∃ shape :
        {shape : Lemma5DerivativeShape //
          theorem4SurgeAllowedLemma5Shape shape},
        GN21MeasuredRightMarginalFeasiblePolicyCanonicalDominanceData
          μ arrival switch12 switch21 w ρ shape.1

/--
Measured marginal canonical-dominance data imply the exact allowed Lemma 5
policy-form certificate consumed by the paper-facing Theorem 4 endpoints.
-/
noncomputable def Theorem4AllMeasurableGN21MarginalFeasiblePolicyCanonicalDominanceData.to_allowed_policy_forms
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableGN21MarginalFeasiblePolicyCanonicalDominanceData
        μ arrival switch12 switch21 w) :
    Theorem4AllMeasurableAllowedPolicyFormsCertificate
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w) where
  exists_optimal := D.exists_optimal
  only_policy_forms := by
    intro ρ hρ
    rcases D.nonsurge ρ hρ with ⟨nshape, ndata⟩
    rcases D.surge ρ hρ with ⟨sshape, sdata⟩
    exact
      ⟨⟨nshape.1, nshape.2, ndata.to_policy_form hρ⟩,
        ⟨sshape.1, sshape.2, sdata.to_policy_form hρ⟩⟩

/--
GN21 measured marginal canonical-dominance data imply the measurable Theorem 4
structural endpoint without assuming the dynamic reward is a positive-affine
transform of the marginal integral.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_of_gn21_marginal_feasible_policy_canonical_dominance
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableGN21MarginalFeasiblePolicyCanonicalDominanceData
        μ arrival switch12 switch21 w) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρstar ∧
        theorem4NonsurgeShape (ρstar 0) ∧
        theorem4SurgeShape (ρstar 1) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ →
          theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) :=
  paper_theorem4_measurable_dynamic_structural_policy_of_allowed_policy_forms
    (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
    D.to_allowed_policy_forms

/--
GN21 measured marginal canonical-dominance data imply the source
a.e.-representative Theorem 4 statement.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_marginal_feasible_policy_canonical_dominance
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableGN21MarginalFeasiblePolicyCanonicalDominanceData
        μ arrival switch12 switch21 w) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_allowed_policy_forms
    μ
    (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
    D.to_allowed_policy_forms

/--
Non-surge fixed-response source data produce the measured-marginal
canonical-dominance package directly.  This is the source-faithful route for
Theorem 4: the objective is the frozen-state Lemma 5 marginal integral itself,
not an asserted positive-affine continuation reward.
-/
noncomputable def GN21MeasuredLeftFixedResponsePolicyFormSourceData.to_marginal_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    (D :
      GN21MeasuredLeftFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hσ_open : IsOpen (ρ 0))
    (hcont :
      GN21SymmDiffContinuousAt (μ 0)
        (lemma5MarginalSetReward (μ 0)
          (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
            (ρ 0) (ρ 1)))
        (ρ 0))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape (ρ 0) →
        0 <
          μ 0
            (lemma5PositiveResponsePolicy
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) \
              ρ 0) ∨
        0 <
          μ 0
            (Function.support
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) ∩
              (ρ 0 \
                lemma5PositiveResponsePolicy
                  (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                    (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                    (ρ 0) (ρ 1))))) :
    GN21MeasuredLeftMarginalFeasiblePolicyCanonicalDominanceData
      μ arrival switch12 switch21 w ρ shape where
  marginal_canonical_dominance :=
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal
      (μ 0)
      (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
        (ρ 0) (ρ 1))
      (ρ 0) shape hσ_open (hρ.1 0).1 hcont
      (D.to_fixed_response hρ).response_measurable
      (D.to_fixed_response hρ).response_integrable_acceptAll
      (D.to_fixed_response hρ).policy_form_data.policy_form hstrict_mass
  arrival_pos := D.arrival_pos
  current_nondegenerate := D.current_nondegenerate
  candidate_nondegenerate := D.candidate_nondegenerate
  denominator_pos := D.hden_pos
  candidate_denominator_pos := D.candidate_den_pos
  q_integrable := D.q_integrable
  payment_integrable := D.w_integrable
  time_integrable := D.time_integrable

/--
Surge fixed-response source data produce the measured-marginal
canonical-dominance package directly, with the non-surge policy frozen.
-/
noncomputable def GN21MeasuredRightFixedResponsePolicyFormSourceData.to_marginal_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    (D :
      GN21MeasuredRightFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hσ_open : IsOpen (ρ 1))
    (hcont :
      GN21SymmDiffContinuousAt (μ 1)
        (lemma5MarginalSetReward (μ 1)
          (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
            (ρ 0) (ρ 1)))
        (ρ 1))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape (ρ 1) →
        0 <
          μ 1
            (lemma5PositiveResponsePolicy
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) \
              ρ 1) ∨
        0 <
          μ 1
            (Function.support
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) ∩
              (ρ 1 \
                lemma5PositiveResponsePolicy
                  (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                    (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                    (ρ 0) (ρ 1))))) :
    GN21MeasuredRightMarginalFeasiblePolicyCanonicalDominanceData
      μ arrival switch12 switch21 w ρ shape where
  marginal_canonical_dominance :=
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal
      (μ 1)
      (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
        (ρ 0) (ρ 1))
      (ρ 1) shape hσ_open (hρ.1 1).1 hcont
      (D.to_fixed_response hρ).response_measurable
      (D.to_fixed_response hρ).response_integrable_acceptAll
      (D.to_fixed_response hρ).policy_form_data.policy_form hstrict_mass
  arrival_pos := D.arrival_pos
  current_nondegenerate := D.current_nondegenerate
  candidate_nondegenerate := D.candidate_nondegenerate
  denominator_pos := D.hden_pos
  candidate_denominator_pos := D.candidate_den_pos
  q_integrable := D.q_integrable
  payment_integrable := D.w_integrable
  time_integrable := D.time_integrable

/-!
## All-optima measured-marginal GN21 fixed-response route

The next package is the corrected exact-form frontier.  It keeps the useful
fixed-response source records, current openness, continuity, and strict-mass
fields, but the canonical-dominance objective is the measured marginal Lemma 5
integral itself.
-/

/--
Non-surge source data for direct measured-marginal canonical dominance.
-/
structure GN21MeasuredLeftFixedResponseMarginalPolicyCanonicalDominanceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy)
    (shape : Lemma5DerivativeShape) where
  source :
    GN21MeasuredLeftFixedResponsePolicyFormSourceData μ arrival switch12
      switch21 w ρ shape
  current_open : IsOpen (ρ 0)
  marginal_continuous :
    GN21SymmDiffContinuousAt (μ 0)
      (lemma5MarginalSetReward (μ 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)))
      (ρ 0)
  strict_mass :
    ¬ lemma5PolicyForm shape (ρ 0) →
      0 <
        μ 0
          (lemma5PositiveResponsePolicy
              (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) \
            ρ 0) ∨
      0 <
        μ 0
          (Function.support
              (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) ∩
            (ρ 0 \
              lemma5PositiveResponsePolicy
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1))))

/-- Convert non-surge direct marginal data to the Theorem 4 marginal package. -/
noncomputable def GN21MeasuredLeftFixedResponseMarginalPolicyCanonicalDominanceData.to_marginal_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    (D :
      GN21MeasuredLeftFixedResponseMarginalPolicyCanonicalDominanceData
        μ arrival switch12 switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ) :
    GN21MeasuredLeftMarginalFeasiblePolicyCanonicalDominanceData
      μ arrival switch12 switch21 w ρ shape :=
  D.source.to_marginal_feasible_policy_canonical_dominance hρ
    D.current_open D.marginal_continuous D.strict_mass

/--
Surge source data for direct measured-marginal canonical dominance.
-/
structure GN21MeasuredRightFixedResponseMarginalPolicyCanonicalDominanceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy)
    (shape : Lemma5DerivativeShape) where
  source :
    GN21MeasuredRightFixedResponsePolicyFormSourceData μ arrival switch12
      switch21 w ρ shape
  current_open : IsOpen (ρ 1)
  marginal_continuous :
    GN21SymmDiffContinuousAt (μ 1)
      (lemma5MarginalSetReward (μ 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)))
      (ρ 1)
  strict_mass :
    ¬ lemma5PolicyForm shape (ρ 1) →
      0 <
        μ 1
          (lemma5PositiveResponsePolicy
              (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) \
            ρ 1) ∨
      0 <
        μ 1
          (Function.support
              (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) ∩
            (ρ 1 \
              lemma5PositiveResponsePolicy
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1))))

/-- Convert surge direct marginal data to the Theorem 4 marginal package. -/
noncomputable def GN21MeasuredRightFixedResponseMarginalPolicyCanonicalDominanceData.to_marginal_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    (D :
      GN21MeasuredRightFixedResponseMarginalPolicyCanonicalDominanceData
        μ arrival switch12 switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ) :
    GN21MeasuredRightMarginalFeasiblePolicyCanonicalDominanceData
      μ arrival switch12 switch21 w ρ shape :=
  D.source.to_marginal_feasible_policy_canonical_dominance hρ
    D.current_open D.marginal_continuous D.strict_mass

/--
All-optima GN21 fixed-response data for the direct measured-marginal
canonical-dominance route.
-/
structure Theorem4AllMeasurableGN21FixedResponseMarginalPolicyCanonicalDominanceData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ
  nonsurge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4NonsurgeAllowedLemma5Shape shape},
        GN21MeasuredLeftFixedResponseMarginalPolicyCanonicalDominanceData
          μ arrival switch12 switch21 w ρ shape.1
  surge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4SurgeAllowedLemma5Shape shape},
        GN21MeasuredRightFixedResponseMarginalPolicyCanonicalDominanceData
          μ arrival switch12 switch21 w ρ shape.1

/--
The all-optima fixed-response marginal package produces the measured-marginal
Theorem 4 input without any positive-affine continuation-objective fields.
-/
noncomputable def Theorem4AllMeasurableGN21FixedResponseMarginalPolicyCanonicalDominanceData.to_marginal_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    (D :
      Theorem4AllMeasurableGN21FixedResponseMarginalPolicyCanonicalDominanceData
        μ arrival switch12 switch21 w) :
    Theorem4AllMeasurableGN21MarginalFeasiblePolicyCanonicalDominanceData
      μ arrival switch12 switch21 w where
  exists_optimal := D.exists_optimal
  nonsurge := by
    intro ρ hρ
    rcases D.nonsurge ρ hρ with ⟨shape, H⟩
    exact ⟨shape, H.to_marginal_feasible_policy_canonical_dominance hρ⟩
  surge := by
    intro ρ hρ
    rcases D.surge ρ hρ with ⟨shape, H⟩
    exact ⟨shape, H.to_marginal_feasible_policy_canonical_dominance hρ⟩

/--
GN21 fixed-response measured-marginal data imply the measurable Theorem 4
structural endpoint.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_of_gn21_fixed_response_marginal_policy_canonical_dominance
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableGN21FixedResponseMarginalPolicyCanonicalDominanceData
        μ arrival switch12 switch21 w) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρstar ∧
        theorem4NonsurgeShape (ρstar 0) ∧
        theorem4SurgeShape (ρstar 1) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ →
          theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) :=
  paper_theorem4_measurable_dynamic_structural_policy_of_gn21_marginal_feasible_policy_canonical_dominance
    μ arrival switch12 switch21 w
    D.to_marginal_feasible_policy_canonical_dominance

/--
GN21 fixed-response measured-marginal data imply the source
a.e.-representative Theorem 4 statement.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_fixed_response_marginal_policy_canonical_dominance
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableGN21FixedResponseMarginalPolicyCanonicalDominanceData
        μ arrival switch12 switch21 w) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_marginal_feasible_policy_canonical_dominance
    μ arrival switch12 switch21 w
    D.to_marginal_feasible_policy_canonical_dominance

/--
Left-state GN21 fixed-response data feed the feasible policy-canonical Lemma 5
route once the source proof supplies the continuous strict-mass and positive
affine objective-transfer facts.
-/
def GN21MeasuredLeftFixedResponsePolicyFormSourceData.to_feasible_policy_canonical_dominance_positive_affine
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    (D :
      GN21MeasuredLeftFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hσ_open : IsOpen (ρ 0))
    (hσ_subset : ρ 0 ⊆ acceptAllPolicy)
    (hcont : GN21SymmDiffContinuousAt (μ 0) Rhat (ρ 0))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape (ρ 0) →
        0 <
          μ 0
            (lemma5PositiveResponsePolicy
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) \
              ρ 0) ∨
        0 <
          μ 0
            (Function.support
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) ∩
              (ρ 0 \
                lemma5PositiveResponsePolicy
                  (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                    (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                    (ρ 0) (ρ 1)))))
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ =
            scale *
              lemma5MarginalSetReward (μ 0)
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) σ + offset) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 0) Rhat (ρ 0) shape :=
  Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal_positive_affine
    (μ 0)
    (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (ρ 0) (ρ 1))
    (ρ 0) shape hσ_open hσ_subset
    hcont (D.to_fixed_response hρ).response_measurable
    (D.to_fixed_response hρ).response_integrable_acceptAll
    (D.to_fixed_response hρ).policy_form_data.policy_form hstrict_mass scale offset
    hscale_pos haffine

/--
Left-state GN21 fixed-response data feed the a.e. Lemma 5 representative route
through any positive-affine local continuation objective.  Unlike
`to_feasible_policy_canonical_dominance_positive_affine`, this follows the
source's null-boundary convention and does not require an exact strict-mass
witness.
-/
def GN21MeasuredLeftFixedResponsePolicyFormSourceData.to_feasible_policy_form_ae_positive_affine
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    [NoAtoms (μ 0)]
    (D :
      GN21MeasuredLeftFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ =
            scale *
              lemma5MarginalSetReward (μ 0)
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) σ + offset)
    (hoptimal :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ ≤ Rhat (ρ 0)) :
    Lemma5FeasiblePolicyFormAlmostEverywhereData (μ 0) shape (ρ 0) :=
  let F := D.to_fixed_response hρ
  F.policy_form_data.feasiblePolicyFormAlmostEverywhere_of_positive_affine_feasible_optimal
    (μ 0) (ρ 0) F.response_measurable F.response_integrable_acceptAll
    (hρ.1 0).2 (hρ.1 0).1 scale offset hscale_pos haffine hoptimal

/--
Right-state GN21 fixed-response data feed the feasible policy-canonical Lemma
5 route once the source proof supplies continuous strict-mass and positive
affine objective-transfer facts.
-/
def GN21MeasuredRightFixedResponsePolicyFormSourceData.to_feasible_policy_canonical_dominance_positive_affine
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    (D :
      GN21MeasuredRightFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hσ_open : IsOpen (ρ 1))
    (hσ_subset : ρ 1 ⊆ acceptAllPolicy)
    (hcont : GN21SymmDiffContinuousAt (μ 1) Rhat (ρ 1))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape (ρ 1) →
        0 <
          μ 1
            (lemma5PositiveResponsePolicy
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) \
              ρ 1) ∨
        0 <
          μ 1
            (Function.support
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) ∩
              (ρ 1 \
                lemma5PositiveResponsePolicy
                  (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                    (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                    (ρ 0) (ρ 1)))))
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ =
            scale *
              lemma5MarginalSetReward (μ 1)
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) σ + offset) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 1) Rhat (ρ 1) shape :=
  Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal_positive_affine
    (μ 1)
    (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (ρ 0) (ρ 1))
    (ρ 1) shape hσ_open hσ_subset
    hcont (D.to_fixed_response hρ).response_measurable
    (D.to_fixed_response hρ).response_integrable_acceptAll
    (D.to_fixed_response hρ).policy_form_data.policy_form hstrict_mass scale offset
    hscale_pos haffine

/--
Right-state GN21 fixed-response data feed the a.e. Lemma 5 representative
route through any positive-affine local continuation objective, without the
extra exact strict-mass side condition required by canonical-dominance data.
-/
def GN21MeasuredRightFixedResponsePolicyFormSourceData.to_feasible_policy_form_ae_positive_affine
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    [NoAtoms (μ 1)]
    (D :
      GN21MeasuredRightFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ =
            scale *
              lemma5MarginalSetReward (μ 1)
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) σ + offset)
    (hoptimal :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ ≤ Rhat (ρ 1)) :
    Lemma5FeasiblePolicyFormAlmostEverywhereData (μ 1) shape (ρ 1) :=
  let F := D.to_fixed_response hρ
  F.policy_form_data.feasiblePolicyFormAlmostEverywhere_of_positive_affine_feasible_optimal
    (μ 1) (ρ 1) F.response_measurable F.response_integrable_acceptAll
    (hρ.1 1).2 (hρ.1 1).1 scale offset hscale_pos haffine hoptimal

/-!
## All-optima positive-affine GN21 fixed-response route

The previous adapters are statewise.  The following bundled source data is the
paper-facing all-optima bridge: for every measurable dynamic optimum, a GN21
fixed-response source record plus the continuous positive-affine objective
identification produces the feasible policy-canonical Lemma 5 dominance data
that Theorem 4 now consumes.
-/

/--
Left-state source data for the feasible policy-canonical Lemma 5 route.  It
combines the GN21 fixed-response policy-form source record with the
positive-affine continuation-objective transfer and the strict-mass witness
needed by exact canonical dominance.
-/
structure GN21MeasuredLeftFixedResponsePolicyCanonicalDominancePositiveAffineData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy)
    (shape : Lemma5DerivativeShape)
    (Rhat : SingleStateReward) where
  source :
    GN21MeasuredLeftFixedResponsePolicyFormSourceData μ arrival switch12
      switch21 w ρ shape
  current_open : IsOpen (ρ 0)
  reward_continuous : GN21SymmDiffContinuousAt (μ 0) Rhat (ρ 0)
  strict_mass :
    ¬ lemma5PolicyForm shape (ρ 0) →
      0 <
        μ 0
          (lemma5PositiveResponsePolicy
              (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) \
            ρ 0) ∨
      0 <
        μ 0
          (Function.support
              (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) ∩
            (ρ 0 \
              lemma5PositiveResponsePolicy
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1))))
  scale : ℝ
  offset : ℝ
  scale_pos : 0 < scale
  affine :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        Rhat σ =
          scale *
            lemma5MarginalSetReward (μ 0)
              (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) σ + offset

/-- Left-state positive-affine GN21 data produce feasible policy-canonical dominance. -/
def GN21MeasuredLeftFixedResponsePolicyCanonicalDominancePositiveAffineData.to_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    (D :
      GN21MeasuredLeftFixedResponsePolicyCanonicalDominancePositiveAffineData
        μ arrival switch12 switch21 w ρ shape Rhat)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 0) Rhat (ρ 0) shape :=
  D.source.to_feasible_policy_canonical_dominance_positive_affine
    hρ D.current_open (hρ.1 0).1 D.reward_continuous D.strict_mass
    D.scale D.offset D.scale_pos D.affine

/--
Right-state source data for the feasible policy-canonical Lemma 5 route.  This
is the state-swapped counterpart of
`GN21MeasuredLeftFixedResponsePolicyCanonicalDominancePositiveAffineData`.
-/
structure GN21MeasuredRightFixedResponsePolicyCanonicalDominancePositiveAffineData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy)
    (shape : Lemma5DerivativeShape)
    (Rhat : SingleStateReward) where
  source :
    GN21MeasuredRightFixedResponsePolicyFormSourceData μ arrival switch12
      switch21 w ρ shape
  current_open : IsOpen (ρ 1)
  reward_continuous : GN21SymmDiffContinuousAt (μ 1) Rhat (ρ 1)
  strict_mass :
    ¬ lemma5PolicyForm shape (ρ 1) →
      0 <
        μ 1
          (lemma5PositiveResponsePolicy
              (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) \
            ρ 1) ∨
      0 <
        μ 1
          (Function.support
              (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) ∩
            (ρ 1 \
              lemma5PositiveResponsePolicy
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1))))
  scale : ℝ
  offset : ℝ
  scale_pos : 0 < scale
  affine :
    ∀ σ : TripPolicy,
      σ ⊆ acceptAllPolicy →
      MeasurableSet σ →
        Rhat σ =
          scale *
            lemma5MarginalSetReward (μ 1)
              (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                (ρ 0) (ρ 1)) σ + offset

/-- Right-state positive-affine GN21 data produce feasible policy-canonical dominance. -/
def GN21MeasuredRightFixedResponsePolicyCanonicalDominancePositiveAffineData.to_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    (D :
      GN21MeasuredRightFixedResponsePolicyCanonicalDominancePositiveAffineData
        μ arrival switch12 switch21 w ρ shape Rhat)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 1) Rhat (ρ 1) shape :=
  D.source.to_feasible_policy_canonical_dominance_positive_affine
    hρ D.current_open (hρ.1 1).1 D.reward_continuous D.strict_mass
    D.scale D.offset D.scale_pos D.affine

/--
All-optima GN21 fixed-response source data plus positive-affine transfer data.
This is the source-facing object that directly implies the feasible
policy-canonical Lemma 5 certificate consumed by the strongest Theorem 4
frontier.
-/
structure Theorem4AllMeasurableGN21FixedResponsePolicyCanonicalDominancePositiveAffineData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ
  nonsurge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4NonsurgeAllowedLemma5Shape shape},
        GN21MeasuredLeftFixedResponsePolicyCanonicalDominancePositiveAffineData
          μ arrival switch12 switch21 w ρ shape.1
          (dynamicStateReward
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ 0)
  surge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      Σ shape :
        {shape : Lemma5DerivativeShape //
          theorem4SurgeAllowedLemma5Shape shape},
        GN21MeasuredRightFixedResponsePolicyCanonicalDominancePositiveAffineData
          μ arrival switch12 switch21 w ρ shape.1
          (dynamicStateReward
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ 1)

/--
The all-optima positive-affine GN21 package is exactly enough to produce the
feasible policy-canonical Lemma 5 data used by Theorem 4.
-/
def Theorem4AllMeasurableGN21FixedResponsePolicyCanonicalDominancePositiveAffineData.to_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    (D :
      Theorem4AllMeasurableGN21FixedResponsePolicyCanonicalDominancePositiveAffineData
        μ arrival switch12 switch21 w) :
    Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w) where
  exists_optimal := D.exists_optimal
  nonsurge := by
    intro ρ hρ
    rcases D.nonsurge ρ hρ with ⟨shape, H⟩
    exact ⟨shape, H.to_feasible_policy_canonical_dominance hρ⟩
  surge := by
    intro ρ hρ
    rcases D.surge ρ hρ with ⟨shape, H⟩
    exact ⟨shape, H.to_feasible_policy_canonical_dominance hρ⟩

/--
GN21 fixed-response positive-affine data imply the measurable Theorem 4
structural endpoint.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_of_gn21_fixed_response_policy_canonical_dominance_positive_affine
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableGN21FixedResponsePolicyCanonicalDominancePositiveAffineData
        μ arrival switch12 switch21 w) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρstar ∧
        theorem4NonsurgeShape (ρstar 0) ∧
        theorem4SurgeShape (ρstar 1) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ →
          theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) :=
  paper_theorem4_measurable_dynamic_structural_policy_of_feasible_policy_canonical_dominance
    μ (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
    D.to_feasible_policy_canonical_dominance

/--
GN21 fixed-response positive-affine data imply the source a.e.-representative
Theorem 4 statement.
-/
theorem paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_fixed_response_policy_canonical_dominance_positive_affine
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableGN21FixedResponsePolicyCanonicalDominancePositiveAffineData
        μ arrival switch12 switch21 w) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) :=
  paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_policy_canonical_dominance
    μ (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
    D.to_feasible_policy_canonical_dominance

end

end GN21DriverSurgePricing
