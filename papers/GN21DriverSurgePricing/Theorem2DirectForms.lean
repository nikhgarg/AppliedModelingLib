import GN21DriverSurgePricing.Lemma5Variational

/-!
# Direct affine policy-form consequences for GN21 Theorem 2

This module isolates the two affine branches of the source's Theorem 2 that
use Lemmas 7 and 8.  It deliberately proves only the *necessity* direction:
an already optimal source-open one-state continuation policy has the stated
endpoint-complete form.  This avoids treating the source's separate global
optimizer-attainment argument, or its endpoint-continuity assertions, as
assumed policy-form conclusions.

The raw endpoint derivative hypotheses below are the actual local calculus
facts consumed by the Lemma 5 variational argument.  They are not bundled in
a certificate and they do not contain a policy-form or optimizer conclusion.
-/

open AppliedModelingLib
open MeasureTheory
open scoped ENNReal Topology

namespace GN21DriverSurgePricing

noncomputable section

/--
Lemma 8 applied directly to the current fixed-opponent CTMC response.  This
is the analytic branch for a negative-affine non-surge price.
-/
theorem gn21Theorem2_nonsurge_negative_affine_response_strictQuasiConcave
    (response : TripPolicy → TripLength → ℝ) (sigma : TripPolicy)
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hresponse :
      response sigma = fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u
          (m * u + a) Qi Qj Ti Tj Ri Rj)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 ≤ Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    strictQuasiConcaveOnPositive (response sigma) := by
  rw [hresponse]
  exact paper_lemma8_affine_ctmc_response_quasi_concave
    m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
    hstate_weight_pos ha_neg hgap_nonneg hlambdaIJ hsum hTi hTj

/--
Lemma 7 applied directly to the current fixed-opponent CTMC response.  This
is the analytic branch for a positive-affine surge price.
-/
theorem gn21Theorem2_surge_positive_affine_response_strictQuasiConvex
    (response : TripPolicy → TripLength → ℝ) (sigma : TripPolicy)
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hresponse :
      response sigma = fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u
          (m * u + a) Qi Qj Ti Tj Ri Rj)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 ≤ Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    strictQuasiConvexOnPositive (response sigma) := by
  rw [hresponse]
  exact paper_lemma7_affine_ctmc_response_quasi_convex
    m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
    hstate_weight_pos ha_pos hgap_nonneg hlambdaIJ hsum hTi hTj

/--
The source aggregate objective with only the non-surge policy varied.  This
definition is used solely to expose the exact one-state objective consumed by
the direct Lemma 5 argument.
-/
def gn21Theorem2NonsurgeFixedAggregateReward
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (rho : Fin 2 → TripPolicy) : SingleStateReward :=
  fun policy =>
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
      (Function.update rho 0 policy)

/--
The source aggregate objective with only the surge policy varied.  As above,
this is a definition of the actual Appendix-D objective, not a continuity or
policy-form assumption.
-/
def gn21Theorem2SurgeFixedAggregateReward
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (rho : Fin 2 → TripPolicy) : SingleStateReward :=
  fun policy =>
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
      (Function.update rho 1 policy)

/--
Changing the non-surge continuation policy on a null set leaves the actual
Appendix-D aggregate objective unchanged.  This is proved by the aggregate
integral congruence theorem, so it introduces no continuity premise.
-/
theorem gn21Theorem2NonsurgeFixedAggregateReward_policy_ae
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (rho : Fin 2 → TripPolicy)
    {left right : TripPolicy}
    (hae : policyAlmostEverywhereEq (mu 0) left right) :
    gn21Theorem2NonsurgeFixedAggregateReward mu arrival switch12 switch21 w rho left =
      gn21Theorem2NonsurgeFixedAggregateReward mu arrival switch12 switch21 w rho right := by
  unfold gn21Theorem2NonsurgeFixedAggregateReward
  have h :=
    gn21AggregateDynamicRewardFunctional_congr_left_policy_ae
      mu arrival switch12 switch21 w
      (ρ := Function.update rho 0 left) (σ0 := right) (by simpa using hae)
  simpa using h

/--
Changing the surge continuation policy on a null set leaves the actual
Appendix-D aggregate objective unchanged.  This is the corresponding direct
right-state integral congruence proof.
-/
theorem gn21Theorem2SurgeFixedAggregateReward_policy_ae
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (rho : Fin 2 → TripPolicy)
    {left right : TripPolicy}
    (hae : policyAlmostEverywhereEq (mu 1) left right) :
    gn21Theorem2SurgeFixedAggregateReward mu arrival switch12 switch21 w rho left =
      gn21Theorem2SurgeFixedAggregateReward mu arrival switch12 switch21 w rho right := by
  unfold gn21Theorem2SurgeFixedAggregateReward
  have h :=
    gn21AggregateDynamicRewardFunctional_congr_right_policy_ae
      mu arrival switch12 switch21 w
      (ρ := Function.update rho 1 left) (σ1 := right) (by simpa using hae)
  simpa using h

/--
The negative-affine non-surge form from Theorem 2, for an already optimal
source-open continuation policy.  The conclusion is the source-complete
middle interval family, so `0` and `infinity` endpoints are retained.

The endpoint hypotheses are local derivative facts for the actual fixed
opponent reward functional.  They are stated directly rather than supplied as
a Theorem-4-style certificate.  No global optimizer-attainment premise or
policy-form premise is used.
-/
theorem gn21Theorem2_nonsurge_negative_affine_openOptimal_has_extended_middle_form
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hoptimal :
      ∀ tau : TripPolicy, IsOpen tau → tau ⊆ acceptAllPolicy →
        Rhat tau ≤ Rhat sigma)
    (hreward_ae :
      ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right)
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (_hm_nonneg : 0 ≤ m)
    (hresponse :
      response sigma = fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u
          (m * u + a) Qi Qj Ti Tj Ri Rj)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 ≤ Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0)
    (hinterval_upper_derivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 ≤ lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (context ∪ Set.Ioo lower x))
              derivativeValue upper ∧
            sameStrictSign derivativeValue
              (response (context ∪ Set.Ioo lower upper) upper))
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy → pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    lemma5SourcePolicyForm .strictlyQuasiConcave sigma := by
  by_cases hsigma_empty : sigma = ∅
  · subst sigma
    exact ⟨∞, 0, by simp⟩
  · have hsigma_nonempty : sigma.Nonempty := by
      by_contra hnot_nonempty
      exact hsigma_empty (Set.not_nonempty_iff_eq_empty.mp hnot_nonempty)
    by_contra hnot_form
    have hshape : strictQuasiConcaveOnPositive (response sigma) :=
      gn21Theorem2_nonsurge_negative_affine_response_strictQuasiConcave
        response sigma m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI hresponse
        hstate_weight_pos ha_neg hgap_nonneg hlambdaIJ hsum hTi hTj
    rcases exists_strictlyQuasiConcave_open_strict_improvement_of_not_form
        mu Rhat response hsigma_open hsigma_subset hsigma_nonempty hnot_form
        hreward_ae
        hshape
        (gn21Lemma5ComponentUpperDerivativeCondition_of_arbitraryContext
          Rhat response hinterval_upper_derivative)
        hopen_split_lower_derivative with
      ⟨improved, himproved_open, himproved_subset, himproved_reward⟩
    exact (not_lt_of_ge (hoptimal improved himproved_open himproved_subset))
      himproved_reward

/--
The positive-affine surge form from Theorem 2, for an already optimal
source-open continuation policy.  The conclusion is the source-complete
two-tail family, including the empty and accept-all endpoint cases.

As in the negative-affine theorem, the endpoint derivative assumptions are
the actual local calculus obligations.  They are intentionally not hidden in
an optimizer, continuity, or policy-form record.
-/
theorem gn21Theorem2_surge_positive_affine_openOptimal_has_extended_twoTail_form
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hoptimal :
      ∀ tau : TripPolicy, IsOpen tau → tau ⊆ acceptAllPolicy →
        Rhat tau ≤ Rhat sigma)
    (hreward_ae :
      ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right)
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (_hm_nonneg : 0 ≤ m)
    (hresponse :
      response sigma = fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u
          (m * u + a) Qi Qj Ti Tj Ri Rj)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 ≤ Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0)
    (hinterval_upper_derivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 ≤ lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (context ∪ Set.Ioo lower x))
              derivativeValue upper ∧
            sameStrictSign derivativeValue
              (response (context ∪ Set.Ioo lower upper) upper))
    (hinterval_lower_derivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 < lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (context ∪ Set.Ioo x upper))
              derivativeValue lower ∧
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioo lower upper) lower))
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy → pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    lemma5SourcePolicyForm .strictlyQuasiConvex sigma := by
  by_cases hsigma_empty : sigma = ∅
  · subst sigma
    exact ⟨0, ∞, by simp⟩
  · have hsigma_nonempty : sigma.Nonempty := by
      by_contra hnot_nonempty
      exact hsigma_empty (Set.not_nonempty_iff_eq_empty.mp hnot_nonempty)
    by_contra hnot_form
    have hshape : strictQuasiConvexOnPositive (response sigma) :=
      gn21Theorem2_surge_positive_affine_response_strictQuasiConvex
        response sigma m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI hresponse
        hstate_weight_pos ha_pos hgap_nonneg hlambdaIJ hsum hTi hTj
    rcases exists_strictlyQuasiConvex_open_strict_improvement_of_not_form
        mu Rhat response hsigma_open hsigma_subset hsigma_nonempty hnot_form
        hreward_ae
        hshape
        (gn21Lemma5ComponentUpperDerivativeCondition_of_arbitraryContext
          Rhat response hinterval_upper_derivative)
        (gn21Lemma5ComponentLowerDerivativeCondition_of_arbitraryContext
          Rhat response hinterval_lower_derivative)
        hopen_split_lower_derivative with
      ⟨improved, himproved_open, himproved_subset, himproved_reward⟩
    exact (not_lt_of_ge (hoptimal improved himproved_open himproved_subset))
      himproved_reward

/--
Concrete non-surge version of the direct affine form theorem.  Here the
single-state reward is definitionally the actual Appendix-D aggregate reward
with state 1 held fixed.  Its null-set invariance is discharged directly by
`gn21AggregateDynamicRewardFunctional_congr_left_policy_ae`, rather than
being supplied as a continuity, optimizer, or policy-form premise.

The remaining derivative hypotheses are the raw endpoint-calculus obligations
for this exact aggregate functional.  They are kept explicit because they are
the part of the source proof still requiring a measure-theoretic derivation.
-/
theorem gn21Theorem2_nonsurge_negative_affine_aggregateOpenOptimal_has_extended_middle_form
    (mu : Fin 2 → Measure TripLength) [NoAtoms (mu 0)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (rho : Fin 2 → TripPolicy)
    (hrho : dynamicOpenOptimal
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho)
    (response : TripPolicy → TripLength → ℝ)
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hm_nonneg : 0 ≤ m)
    (hresponse :
      response (rho 0) = fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u
          (m * u + a) Qi Qj Ti Tj Ri Rj)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 ≤ Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0)
    (hinterval_upper_derivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 ≤ lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                gn21Theorem2NonsurgeFixedAggregateReward
                  mu arrival switch12 switch21 w rho
                  (context ∪ Set.Ioo lower x))
              derivativeValue upper ∧
            sameStrictSign derivativeValue
              (response (context ∪ Set.Ioo lower upper) upper))
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy → pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                gn21Theorem2NonsurgeFixedAggregateReward
                  mu arrival switch12 switch21 w rho
                  (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    lemma5SourcePolicyForm .strictlyQuasiConcave (rho 0) := by
  exact
    gn21Theorem2_nonsurge_negative_affine_openOptimal_has_extended_middle_form
      (mu 0)
      (gn21Theorem2NonsurgeFixedAggregateReward
        mu arrival switch12 switch21 w rho)
      response
      (hsigma_open := (hrho.1 0).2)
      (hsigma_subset := (hrho.1 0).1)
      (hoptimal := by
        intro tau htau_open htau_subset
        apply hrho.2 (Function.update rho 0 tau)
        intro i
        fin_cases i
        · simpa using ⟨htau_subset, htau_open⟩
        · simpa using hrho.1 1)
      (hreward_ae := by
        intro left right hae
        exact
          gn21Theorem2NonsurgeFixedAggregateReward_policy_ae
            mu arrival switch12 switch21 w rho hae)
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI hm_nonneg hresponse
      hstate_weight_pos ha_neg hgap_nonneg hlambdaIJ hsum hTi hTj
      hinterval_upper_derivative hopen_split_lower_derivative

/--
Concrete surge version of the direct affine form theorem.  It holds state 0
fixed in the actual Appendix-D aggregate objective and discharges the
null-set equality premise by the direct right-policy aggregate congruence
theorem.  No endpoint-continuity package or policy-form conclusion is used.

As in the non-surge wrapper, the displayed derivative hypotheses are the raw
measure-theoretic obligations that remain to be derived from the source's
density regularity.
-/
theorem gn21Theorem2_surge_positive_affine_aggregateOpenOptimal_has_extended_twoTail_form
    (mu : Fin 2 → Measure TripLength) [NoAtoms (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (rho : Fin 2 → TripPolicy)
    (hrho : dynamicOpenOptimal
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho)
    (response : TripPolicy → TripLength → ℝ)
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hm_nonneg : 0 ≤ m)
    (hresponse :
      response (rho 1) = fun u : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI u) u
          (m * u + a) Qi Qj Ti Tj Ri Rj)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 ≤ Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0)
    (hinterval_upper_derivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 ≤ lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                gn21Theorem2SurgeFixedAggregateReward
                  mu arrival switch12 switch21 w rho
                  (context ∪ Set.Ioo lower x))
              derivativeValue upper ∧
            sameStrictSign derivativeValue
              (response (context ∪ Set.Ioo lower upper) upper))
    (hinterval_lower_derivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 < lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                gn21Theorem2SurgeFixedAggregateReward
                  mu arrival switch12 switch21 w rho
                  (context ∪ Set.Ioo x upper))
              derivativeValue lower ∧
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioo lower upper) lower))
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy → pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                gn21Theorem2SurgeFixedAggregateReward
                  mu arrival switch12 switch21 w rho
                  (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    lemma5SourcePolicyForm .strictlyQuasiConvex (rho 1) := by
  exact
    gn21Theorem2_surge_positive_affine_openOptimal_has_extended_twoTail_form
      (mu 1)
      (gn21Theorem2SurgeFixedAggregateReward
        mu arrival switch12 switch21 w rho)
      response
      (hsigma_open := (hrho.1 1).2)
      (hsigma_subset := (hrho.1 1).1)
      (hoptimal := by
        intro tau htau_open htau_subset
        apply hrho.2 (Function.update rho 1 tau)
        intro i
        fin_cases i
        · simpa using hrho.1 0
        · simpa using ⟨htau_subset, htau_open⟩)
      (hreward_ae := by
        intro left right hae
        exact
          gn21Theorem2SurgeFixedAggregateReward_policy_ae
            mu arrival switch12 switch21 w rho hae)
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI hm_nonneg hresponse
      hstate_weight_pos ha_pos hgap_nonneg hlambdaIJ hsum hTi hTj
      hinterval_upper_derivative hinterval_lower_derivative
      hopen_split_lower_derivative

end

end GN21DriverSurgePricing
