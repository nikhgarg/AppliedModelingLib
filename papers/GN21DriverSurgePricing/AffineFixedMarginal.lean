import GN21DriverSurgePricing.Lemma5Variational
import GN21DriverSurgePricing.Theorem4MarginalOptimality
import GN21DriverSurgePricing.Theorem4OptimalMass

/-!
# Source-exact fixed-marginal route for GN21 affine policy forms

This module contains the part of the Lemma 5 argument that is valid directly
on the actual aggregate model: global dynamic optimality gives optimality of a
fixed marginal set reward, and that optimum agrees a.e. with its
positive-response set.  It deliberately does not use endpoint derivatives of
set-union paths.

The remaining affine analysis has two explicit obligations: identify the
positive-response set with an endpoint-complete source policy, and prove that
the zero-response boundary is null.  Keeping those obligations as ordinary
propositions prevents them from being hidden in a variation certificate.
-/

namespace GN21DriverSurgePricing

open MeasureTheory

/--
The source-exact fixed-marginal conclusion.  Unlike the legacy finite-endpoint
predicate, `lemma5SourcePolicyForm` represents the printed infinity endpoints.
-/
theorem lemma5SourcePolicyFormAlmostEverywhere_of_positiveResponse_candidate_le
    (mu : Measure TripLength)
    (response : TripLength -> Real)
    (shape : Lemma5DerivativeShape)
    (sigma : TripPolicy)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy mu)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hpositive_response_form :
      lemma5SourcePolicyForm shape (lemma5PositiveResponsePolicy response))
    (hpositive_zero_set_null :
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0)
    (hcandidate :
      lemma5MarginalSetReward mu response
          (lemma5PositiveResponsePolicy response) <=
        lemma5MarginalSetReward mu response sigma) :
    lemma5SourcePolicyFormAlmostEverywhere mu shape sigma := by
  let positivePolicy : TripPolicy := lemma5PositiveResponsePolicy response
  have hpositive_omitted : mu (positivePolicy \ sigma) = 0 := by
    simpa only [positivePolicy] using
      lemma5_positiveResponse_omitted_mass_zero_of_candidate_le
        mu response sigma hresponse_measurable hresponse_integrable_acceptAll
        hsigma_measurable hsigma_subset hcandidate
  have hnegative_accepted :
      mu (Function.support response ∩ (sigma \ positivePolicy)) = 0 := by
    simpa only [positivePolicy] using
      lemma5_positiveResponse_negative_mass_zero_of_candidate_le
        mu response sigma hresponse_measurable hresponse_integrable_acceptAll
        hsigma_measurable hsigma_subset hcandidate
  have hsigma_minus_positive_subset :
      sigma \ positivePolicy ⊆
        Function.support response ∩ (sigma \ positivePolicy) ∪
          {tau : TripLength | 0 < tau /\ response tau = 0} := by
    intro tau htau
    by_cases hzero : response tau = 0
    · exact Or.inr <| by
        exact ⟨hsigma_subset htau.1, hzero⟩
    · exact Or.inl ⟨hzero, htau⟩
  have hsigma_minus_positive : mu (sigma \ positivePolicy) = 0 :=
    measure_mono_null hsigma_minus_positive_subset
      (measure_union_null hnegative_accepted hpositive_zero_set_null)
  refine ⟨positivePolicy, ?_, ?_⟩
  · simpa only [positivePolicy] using hpositive_response_form
  · exact policyAlmostEverywhereEq_of_diff_null mu
      hsigma_minus_positive hpositive_omitted

/--
Global fixed-marginal optimality supplies the comparison needed by the
source-exact a.e. conclusion.  This is the semantic replacement for a local
endpoint-calculus assumption.
-/
theorem lemma5SourcePolicyFormAlmostEverywhere_of_fixedMarginal_optimal
    (mu : Measure TripLength)
    (response : TripLength -> Real)
    (shape : Lemma5DerivativeShape)
    (sigma : TripPolicy)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy mu)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hpositive_response_form :
      lemma5SourcePolicyForm shape (lemma5PositiveResponsePolicy response))
    (hpositive_zero_set_null :
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0)
    (hoptimal :
      forall sigma' : TripPolicy,
        sigma' ⊆ acceptAllPolicy ->
        MeasurableSet sigma' ->
          lemma5MarginalSetReward mu response sigma' <=
            lemma5MarginalSetReward mu response sigma) :
    lemma5SourcePolicyFormAlmostEverywhere mu shape sigma := by
  apply lemma5SourcePolicyFormAlmostEverywhere_of_positiveResponse_candidate_le
    mu response shape sigma hresponse_measurable hresponse_integrable_acceptAll
    hsigma_measurable hsigma_subset hpositive_response_form
    hpositive_zero_set_null
  exact hoptimal (lemma5PositiveResponsePolicy response)
    (lemma5PositiveResponsePolicy_subset_acceptAll response)
    (measurableSet_lemma5PositiveResponsePolicy response hresponse_measurable)

/--
Positive pointwise scaling preserves both the positive-response policy and the
nullity of its zero boundary on feasible trip lengths.  This lets the affine
Lemma 6 analysis operate on its normalized response while the variational
argument operates on the actual measured marginal response.
-/
theorem lemma5SourcePolicyForm_and_zeroSetNull_of_positive_scaling
    (mu : Measure TripLength)
    (base response scale : TripLength -> Real)
    (shape : Lemma5DerivativeShape)
    (hbase_form :
      lemma5SourcePolicyForm shape (lemma5PositiveResponsePolicy base))
    (hbase_zero_set_null :
      mu {tau : TripLength | 0 < tau /\ base tau = 0} = 0)
    (hscale_pos : forall tau : TripLength, 0 < tau -> 0 < scale tau)
    (hresponse_eq :
      forall tau : TripLength, 0 < tau -> response tau = scale tau * base tau) :
    lemma5SourcePolicyForm shape (lemma5PositiveResponsePolicy response) /\
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  have hpositive_policy_eq :
      lemma5PositiveResponsePolicy response = lemma5PositiveResponsePolicy base := by
    ext tau
    constructor
    · intro htau
      refine ⟨htau.1, ?_⟩
      have hproduct_pos : 0 < scale tau * base tau := by
        rw [← hresponse_eq tau htau.1]
        exact htau.2
      rcases (mul_pos_iff.mp hproduct_pos) with hpositive | hnegative
      · exact hpositive.2
      · exact False.elim (not_lt_of_ge (le_of_lt (hscale_pos tau htau.1))
          hnegative.1)
    · intro htau
      refine ⟨htau.1, ?_⟩
      rw [hresponse_eq tau htau.1]
      exact mul_pos (hscale_pos tau htau.1) htau.2
  have hresponse_zero_subset_base_zero :
      {tau : TripLength | 0 < tau /\ response tau = 0} ⊆
        {tau : TripLength | 0 < tau /\ base tau = 0} := by
    intro tau htau
    refine ⟨htau.1, ?_⟩
    have hproduct_zero : scale tau * base tau = 0 := by
      rw [← hresponse_eq tau htau.1]
      exact htau.2
    exact (mul_eq_zero.mp hproduct_zero).resolve_left
      (ne_of_gt (hscale_pos tau htau.1))
  constructor
  · rwa [hpositive_policy_eq]
  · exact measure_mono_null hresponse_zero_subset_base_zero hbase_zero_set_null

/--
Positive scaling also preserves the repaired increasing-branch alternative:
either the base positive-response set has the literal finite source form, or
it is empty.  The statement is intentionally disjunctive because a positive
scale cannot turn an empty positive-response set into a finite cutoff.
-/
theorem lemma5SourcePolicyForm_or_positiveResponse_empty_and_zeroSetNull_of_positive_scaling
    (mu : Measure TripLength)
    (base response scale : TripLength -> Real)
    (hbase_form_or_empty :
      lemma5SourcePolicyForm .strictlyIncreasing
          (lemma5PositiveResponsePolicy base) \/
        lemma5PositiveResponsePolicy base = ∅)
    (hbase_zero_set_null :
      mu {tau : TripLength | 0 < tau /\ base tau = 0} = 0)
    (hscale_pos : forall tau : TripLength, 0 < tau -> 0 < scale tau)
    (hresponse_eq :
      forall tau : TripLength, 0 < tau -> response tau = scale tau * base tau) :
    (lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy response) \/
      lemma5PositiveResponsePolicy response = ∅) /\
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  have hpositive_policy_eq :
      lemma5PositiveResponsePolicy response = lemma5PositiveResponsePolicy base := by
    ext tau
    constructor
    · intro htau
      refine ⟨htau.1, ?_⟩
      have hproduct_pos : 0 < scale tau * base tau := by
        rw [← hresponse_eq tau htau.1]
        exact htau.2
      rcases (mul_pos_iff.mp hproduct_pos) with hpositive | hnegative
      · exact hpositive.2
      · exact False.elim (not_lt_of_ge (le_of_lt (hscale_pos tau htau.1))
          hnegative.1)
    · intro htau
      refine ⟨htau.1, ?_⟩
      rw [hresponse_eq tau htau.1]
      exact mul_pos (hscale_pos tau htau.1) htau.2
  have hresponse_zero_subset_base_zero :
      {tau : TripLength | 0 < tau /\ response tau = 0} ⊆
        {tau : TripLength | 0 < tau /\ base tau = 0} := by
    intro tau htau
    refine ⟨htau.1, ?_⟩
    have hproduct_zero : scale tau * base tau = 0 := by
      rw [← hresponse_eq tau htau.1]
      exact htau.2
    exact (mul_eq_zero.mp hproduct_zero).resolve_left
      (ne_of_gt (hscale_pos tau htau.1))
  constructor
  · rcases hbase_form_or_empty with hform | hempty
    · exact Or.inl (by rwa [hpositive_policy_eq])
    · exact Or.inr (by rwa [hpositive_policy_eq])
  · exact measure_mono_null hresponse_zero_subset_base_zero hbase_zero_set_null

/--
Transfer an exact left-state Lemma 6 policy form and null boundary to the
actual Appendix-D marginal response.  All scale and reward-rate equalities are
visible source primitives rather than fields of a certificate.
-/
theorem gn21MeasuredLeft_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    (Ri Rj : Real) (shape : Lemma5DerivativeShape)
    (hbase_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wI sigmaI sigmaJ Ri Rj)))
    (hbase_zero_set_null :
      muI
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI sigmaI sigmaJ Ri Rj tau = 0} = 0)
    (hQj_pos :
      0 < gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI wI sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wI wJ sigmaI sigmaJ)) /\
      muI
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI wJ sigmaI sigmaJ tau = 0} = 0 := by
  exact lemma5SourcePolicyForm_and_zeroSetNull_of_positive_scaling
    muI
    (gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wI sigmaI sigmaJ Ri Rj)
    (gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wI wJ sigmaI sigmaJ)
    (gn21MeasuredLeftLemma6ScaleAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ)
    shape hbase_form hbase_zero_set_null
    (by
      intro tau htau
      exact gn21MeasuredLeftLemma6ScaleAtCurrent_pos
        muI muJ arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ
        hQj_pos hTi_pos hTj_pos hden_pos htau)
    (by
      intro tau htau
      exact gn21MeasuredLeftMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
        muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ
        Ri Rj tau (ne_of_gt hden_pos) (ne_of_gt htau)
        (ne_of_gt hTi_pos) (ne_of_gt hTj_pos) hWi hWj)

/--
State-swapped version of
`gn21MeasuredLeft_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6`.
-/
theorem gn21MeasuredRight_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    (Ri Rj : Real) (shape : Lemma5DerivativeShape)
    (hbase_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wJ sigmaI sigmaJ Ri Rj)))
    (hbase_zero_set_null :
      muJ
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wJ sigmaI sigmaJ Ri Rj tau = 0} = 0)
    (hQi_pos :
      0 < gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI wI sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wI wJ sigmaI sigmaJ)) /\
      muJ
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI wJ sigmaI sigmaJ tau = 0} = 0 := by
  exact lemma5SourcePolicyForm_and_zeroSetNull_of_positive_scaling
    muJ
    (gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wJ sigmaI sigmaJ Ri Rj)
    (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wI wJ sigmaI sigmaJ)
    (gn21MeasuredRightLemma6ScaleAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ)
    shape hbase_form hbase_zero_set_null
    (by
      intro tau htau
      exact gn21MeasuredRightLemma6ScaleAtCurrent_pos
        muI muJ arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ
        hQi_pos hTi_pos hTj_pos hden_pos htau)
    (by
      intro tau htau
      exact gn21MeasuredRightMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
        muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ
        Ri Rj tau (ne_of_gt hden_pos) (ne_of_gt htau)
        (ne_of_gt hTi_pos) (ne_of_gt hTj_pos) hWi hWj)

/-- A strictly quasi-convex response has no third distinct positive zero. -/
theorem strictQuasiConvex_positiveZero_eq_left_or_right
    (response : TripLength -> Real)
    (hquasi : strictQuasiConvexOnPositive response)
    {left right point : TripLength}
    (hleft : 0 < left /\ response left = 0)
    (hright : 0 < right /\ response right = 0)
    (hleft_right : left < right)
    (hpoint : 0 < point /\ response point = 0) :
    point = left \/ point = right := by
  rcases lt_trichotomy point left with hpoint_left | hpoint_eq_left | hleft_point
  · exfalso
    have hstrict :=
      AppliedModelingLib.StrictQuasiConvexOnPositive.lt_of_between hquasi
        hpoint.1 hpoint_left hleft_right
    rw [hleft.2, hright.2, hpoint.2] at hstrict
    norm_num at hstrict
  · exact Or.inl hpoint_eq_left
  · rcases lt_trichotomy point right with hpoint_right | hpoint_eq_right | hright_point
    · exfalso
      have hstrict :=
        AppliedModelingLib.StrictQuasiConvexOnPositive.lt_of_between hquasi
          hleft.1 hleft_point hpoint_right
      rw [hleft.2, hright.2, hpoint.2] at hstrict
      norm_num at hstrict
    · exact Or.inr hpoint_eq_right
    · exfalso
      have hstrict :=
        AppliedModelingLib.StrictQuasiConvexOnPositive.lt_of_between hquasi
          hleft.1 hleft_right hright_point
      rw [hleft.2, hright.2, hpoint.2] at hstrict
      norm_num at hstrict

/-- A strictly quasi-concave response has no third distinct positive zero. -/
theorem strictQuasiConcave_positiveZero_eq_left_or_right
    (response : TripLength -> Real)
    (hquasi : strictQuasiConcaveOnPositive response)
    {left right point : TripLength}
    (hleft : 0 < left /\ response left = 0)
    (hright : 0 < right /\ response right = 0)
    (hleft_right : left < right)
    (hpoint : 0 < point /\ response point = 0) :
    point = left \/ point = right := by
  rcases lt_trichotomy point left with hpoint_left | hpoint_eq_left | hleft_point
  · exfalso
    have hstrict :=
      AppliedModelingLib.StrictQuasiConcaveOnPositive.lt_between hquasi
        hpoint.1 hpoint_left hleft_right
    rw [hleft.2, hright.2, hpoint.2] at hstrict
    norm_num at hstrict
  · exact Or.inl hpoint_eq_left
  · rcases lt_trichotomy point right with hpoint_right | hpoint_eq_right | hright_point
    · exfalso
      have hstrict :=
        AppliedModelingLib.StrictQuasiConcaveOnPositive.lt_between hquasi
          hleft.1 hleft_point hpoint_right
      rw [hleft.2, hright.2, hpoint.2] at hstrict
      norm_num at hstrict
    · exact Or.inr hpoint_eq_right
    · exfalso
      have hstrict :=
        AppliedModelingLib.StrictQuasiConcaveOnPositive.lt_between hquasi
          hleft.1 hleft_right hright_point
      rw [hleft.2, hright.2, hpoint.2] at hstrict
      norm_num at hstrict

/-- Nonatomic measures assign zero mass to positive zeroes of a strictly quasi-convex response. -/
theorem measure_positiveZeroSet_eq_zero_of_strictQuasiConvex
    (mu : Measure TripLength) [NoAtoms mu]
    (response : TripLength -> Real)
    (hquasi : strictQuasiConvexOnPositive response) :
    mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  classical
  let zeroSet : Set TripLength := {tau : TripLength | 0 < tau /\ response tau = 0}
  change mu zeroSet = 0
  by_cases hzero_empty : zeroSet.Nonempty
  · rcases hzero_empty with ⟨left, hleft⟩
    by_cases hsecond : exists right, right ∈ zeroSet /\ right ≠ left
    · rcases hsecond with ⟨right, hright, hright_ne_left⟩
      have horder : left < right \/ right < left :=
        lt_or_gt_of_ne (Ne.symm hright_ne_left)
      rcases horder with hleft_right | hright_left
      · have hsubset : zeroSet ⊆ ({left} : Set TripLength) ∪ ({right} : Set TripLength) := by
          intro point hpoint
          rcases strictQuasiConvex_positiveZero_eq_left_or_right response hquasi
              hleft hright hleft_right hpoint with hpoint_left | hpoint_right
          · exact Or.inl (Set.mem_singleton_iff.mpr hpoint_left)
          · exact Or.inr (Set.mem_singleton_iff.mpr hpoint_right)
        exact measure_mono_null hsubset
          (measure_union_null (measure_singleton left) (measure_singleton right))
      · have hsubset : zeroSet ⊆ ({left} : Set TripLength) ∪ ({right} : Set TripLength) := by
          intro point hpoint
          rcases strictQuasiConvex_positiveZero_eq_left_or_right response hquasi
              hright hleft hright_left hpoint with hpoint_right | hpoint_left
          · exact Or.inr (Set.mem_singleton_iff.mpr hpoint_right)
          · exact Or.inl (Set.mem_singleton_iff.mpr hpoint_left)
        exact measure_mono_null hsubset
          (measure_union_null (measure_singleton left) (measure_singleton right))
    · have hsubset : zeroSet ⊆ ({left} : Set TripLength) := by
        intro point hpoint
        have hpoint_left : point = left := by
          by_contra hpoint_ne_left
          exact hsecond ⟨point, hpoint, hpoint_ne_left⟩
        exact Set.mem_singleton_iff.mpr hpoint_left
      exact measure_mono_null hsubset (measure_singleton left)
  · rw [Set.not_nonempty_iff_eq_empty.mp hzero_empty]
    simp

/-- Nonatomic measures assign zero mass to positive zeroes of a strictly quasi-concave response. -/
theorem measure_positiveZeroSet_eq_zero_of_strictQuasiConcave
    (mu : Measure TripLength) [NoAtoms mu]
    (response : TripLength -> Real)
    (hquasi : strictQuasiConcaveOnPositive response) :
    mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  classical
  let zeroSet : Set TripLength := {tau : TripLength | 0 < tau /\ response tau = 0}
  change mu zeroSet = 0
  by_cases hzero_empty : zeroSet.Nonempty
  · rcases hzero_empty with ⟨left, hleft⟩
    by_cases hsecond : exists right, right ∈ zeroSet /\ right ≠ left
    · rcases hsecond with ⟨right, hright, hright_ne_left⟩
      have horder : left < right \/ right < left :=
        lt_or_gt_of_ne (Ne.symm hright_ne_left)
      rcases horder with hleft_right | hright_left
      · have hsubset : zeroSet ⊆ ({left} : Set TripLength) ∪ ({right} : Set TripLength) := by
          intro point hpoint
          rcases strictQuasiConcave_positiveZero_eq_left_or_right response hquasi
              hleft hright hleft_right hpoint with hpoint_left | hpoint_right
          · exact Or.inl (Set.mem_singleton_iff.mpr hpoint_left)
          · exact Or.inr (Set.mem_singleton_iff.mpr hpoint_right)
        exact measure_mono_null hsubset
          (measure_union_null (measure_singleton left) (measure_singleton right))
      · have hsubset : zeroSet ⊆ ({left} : Set TripLength) ∪ ({right} : Set TripLength) := by
          intro point hpoint
          rcases strictQuasiConcave_positiveZero_eq_left_or_right response hquasi
              hright hleft hright_left hpoint with hpoint_right | hpoint_left
          · exact Or.inr (Set.mem_singleton_iff.mpr hpoint_right)
          · exact Or.inl (Set.mem_singleton_iff.mpr hpoint_left)
        exact measure_mono_null hsubset
          (measure_union_null (measure_singleton left) (measure_singleton right))
    · have hsubset : zeroSet ⊆ ({left} : Set TripLength) := by
        intro point hpoint
        have hpoint_left : point = left := by
          by_contra hpoint_ne_left
          exact hsecond ⟨point, hpoint, hpoint_ne_left⟩
        exact Set.mem_singleton_iff.mpr hpoint_left
      exact measure_mono_null hsubset (measure_singleton left)
  · rw [Set.not_nonempty_iff_eq_empty.mp hzero_empty]
    simp

/-- A strictly increasing response has at most one positive zero. -/
theorem strictMono_positiveZero_eq
    (response : TripLength -> Real)
    (hmono : StrictMonoOn response (Set.Ioi 0))
    {left point : TripLength}
    (hleft : 0 < left /\ response left = 0)
    (hpoint : 0 < point /\ response point = 0) :
    point = left := by
  rcases lt_trichotomy point left with hpoint_left | hpoint_eq_left | hleft_point
  · have hstrict : response point < response left :=
      hmono hpoint.1 hleft.1 hpoint_left
    rw [hpoint.2, hleft.2] at hstrict
    norm_num at hstrict
  · exact hpoint_eq_left
  · have hstrict : response left < response point :=
      hmono hleft.1 hpoint.1 hleft_point
    rw [hpoint.2, hleft.2] at hstrict
    norm_num at hstrict

/-- A strictly decreasing response has at most one positive zero. -/
theorem strictAnti_positiveZero_eq
    (response : TripLength -> Real)
    (hanti : StrictAntiOn response (Set.Ioi 0))
    {left point : TripLength}
    (hleft : 0 < left /\ response left = 0)
    (hpoint : 0 < point /\ response point = 0) :
    point = left := by
  rcases lt_trichotomy point left with hpoint_left | hpoint_eq_left | hleft_point
  · have hstrict : response left < response point :=
      hanti hpoint.1 hleft.1 hpoint_left
    rw [hpoint.2, hleft.2] at hstrict
    norm_num at hstrict
  · exact hpoint_eq_left
  · have hstrict : response point < response left :=
      hanti hleft.1 hpoint.1 hleft_point
    rw [hpoint.2, hleft.2] at hstrict
    norm_num at hstrict

/-- Nonatomic measures assign zero mass to positive zeroes of a strictly increasing response. -/
theorem measure_positiveZeroSet_eq_zero_of_strictMono
    (mu : Measure TripLength) [NoAtoms mu]
    (response : TripLength -> Real)
    (hmono : StrictMonoOn response (Set.Ioi 0)) :
    mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  classical
  let zeroSet : Set TripLength := {tau : TripLength | 0 < tau /\ response tau = 0}
  change mu zeroSet = 0
  by_cases hzero_nonempty : zeroSet.Nonempty
  · rcases hzero_nonempty with ⟨left, hleft⟩
    have hsubset : zeroSet ⊆ ({left} : Set TripLength) := by
      intro point hpoint
      exact Set.mem_singleton_iff.mpr
        (strictMono_positiveZero_eq response hmono hleft hpoint)
    exact measure_mono_null hsubset (measure_singleton left)
  · rw [Set.not_nonempty_iff_eq_empty.mp hzero_nonempty]
    simp

/-- Nonatomic measures assign zero mass to positive zeroes of a strictly decreasing response. -/
theorem measure_positiveZeroSet_eq_zero_of_strictAnti
    (mu : Measure TripLength) [NoAtoms mu]
    (response : TripLength -> Real)
    (hanti : StrictAntiOn response (Set.Ioi 0)) :
    mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  classical
  let zeroSet : Set TripLength := {tau : TripLength | 0 < tau /\ response tau = 0}
  change mu zeroSet = 0
  by_cases hzero_nonempty : zeroSet.Nonempty
  · rcases hzero_nonempty with ⟨left, hleft⟩
    have hsubset : zeroSet ⊆ ({left} : Set TripLength) := by
      intro point hpoint
      exact Set.mem_singleton_iff.mpr
        (strictAnti_positiveZero_eq response hanti hleft hpoint)
    exact measure_mono_null hsubset (measure_singleton left)
  · rw [Set.not_nonempty_iff_eq_empty.mp hzero_nonempty]
    simp

/--
A strictly increasing response has the printed finite right-cutoff form once
the actual optimality argument has ruled out the all-negative branch.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_strictMonoOn_positive_or_zero
    (response : TripLength -> Real)
    (hmono : StrictMonoOn response (Set.Ioi 0))
    (hpositive_or_zero :
      (forall tau : TripLength, 0 < tau -> 0 < response tau) \/
        exists t : TripLength, 0 < t /\ response t = 0) :
    lemma5SourcePolicyForm .strictlyIncreasing
    (lemma5PositiveResponsePolicy response) := by
  rcases hpositive_or_zero with hpositive | ⟨t, ht_pos, hzero⟩
  · have hpolicy_eq : lemma5PositiveResponsePolicy response = acceptAllPolicy := by
      ext tau
      constructor
      · exact fun htau => htau.1
      · intro htau
        exact ⟨htau, hpositive tau htau⟩
    refine ⟨0, ?_⟩
    simpa [hpolicy_eq]
  · let cutoffNN : NNReal := ⟨t, le_of_lt ht_pos⟩
    refine ⟨cutoffNN, ?_⟩
    have hrejects_short :
        rejectsShortTrips t (lemma5PositiveResponsePolicy response) := by
      intro tau htau_pos
      constructor
      · intro htau_mem
        have htau_response_pos : 0 < response tau := htau_mem.2
        by_contra hnot_lt
        have htau_le_t : tau <= t := le_of_not_gt hnot_lt
        rcases lt_or_eq_of_le htau_le_t with htau_lt_t | htau_eq_t
        · have hresponse_lt : response tau < response t :=
            hmono htau_pos ht_pos htau_lt_t
          linarith
        · have hresponse_zero : response tau = 0 := by
            simpa [htau_eq_t] using hzero
          linarith
      · intro ht_lt_tau
        have hresponse_lt : response t < response tau :=
          hmono ht_pos htau_pos ht_lt_tau
        exact ⟨htau_pos, by linarith⟩
    have hpolicy_eq :
        lemma5PositiveResponsePolicy response = rejectShortTripsPolicy t :=
      eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
        hrejects_short (lemma5PositiveResponsePolicy_subset_acceptAll response)
    simpa [cutoffNN] using hpolicy_eq

/--
A strictly decreasing response has the printed extended left-cutoff form once
it is everywhere positive or has a positive zero.  The first alternative is
the source's infinity endpoint.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_strictAntiOn_positive_or_zero
    (response : TripLength -> Real)
    (hanti : StrictAntiOn response (Set.Ioi 0))
    (hpositive_or_zero :
      (forall tau : TripLength, 0 < tau -> 0 < response tau) \/
        exists t : TripLength, 0 < t /\ response t = 0) :
    lemma5SourcePolicyForm .strictlyDecreasing
      (lemma5PositiveResponsePolicy response) := by
  rcases hpositive_or_zero with hpositive | ⟨t, ht_pos, hzero⟩
  · have hpolicy_eq : lemma5PositiveResponsePolicy response = acceptAllPolicy := by
      ext tau
      constructor
      · exact fun htau => htau.1
      · intro htau
        exact ⟨htau, hpositive tau htau⟩
    refine ⟨(⊤ : ENNReal), ?_⟩
    simpa [hpolicy_eq]
  · let cutoffNN : NNReal := ⟨t, le_of_lt ht_pos⟩
    refine ⟨(cutoffNN : ENNReal), ?_⟩
    have hrejects_long :
        rejectsLongTrips t (lemma5PositiveResponsePolicy response) := by
      intro tau htau_pos
      constructor
      · intro htau_mem
        have htau_response_pos : 0 < response tau := htau_mem.2
        by_contra hnot_lt
        have ht_le_tau : t <= tau := le_of_not_gt hnot_lt
        rcases lt_or_eq_of_le ht_le_tau with ht_lt_tau | ht_eq_tau
        · have hresponse_lt : response tau < response t :=
            hanti ht_pos htau_pos ht_lt_tau
          linarith
        · have hresponse_zero : response tau = 0 := by
            simpa [← ht_eq_tau] using hzero
          linarith
      · intro htau_lt_t
        have hresponse_lt : response t < response tau :=
          hanti htau_pos ht_pos htau_lt_t
        exact ⟨htau_pos, by linarith⟩
    have hpolicy_eq :
        lemma5PositiveResponsePolicy response = rejectLongTripsPolicy t :=
      eq_rejectLongTripsPolicy_of_rejectsLongTrips_of_subset_acceptAll
        hrejects_long (lemma5PositiveResponsePolicy_subset_acceptAll response)
    simpa [cutoffNN] using hpolicy_eq

/--
For a continuous strictly decreasing response, the only possibilities are
everywhere positive, a positive zero, or everywhere negative.  This is a
plain intermediate-value argument, not an endpoint-variation premise.
-/
theorem strictAntiOn_positive_or_zero_or_negative_of_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hanti : StrictAntiOn response (Set.Ioi 0)) :
    (forall tau : TripLength, 0 < tau -> 0 < response tau) \/
      (exists t : TripLength, 0 < t /\ response t = 0) \/
        (forall tau : TripLength, 0 < tau -> response tau < 0) := by
  by_cases hpositive : forall tau : TripLength, 0 < tau -> 0 < response tau
  · exact Or.inl hpositive
  · push Not at hpositive
    rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
    by_cases hzero : exists t : TripLength, 0 < t /\ response t = 0
    · exact Or.inr (Or.inl hzero)
    · refine Or.inr (Or.inr ?_)
      have hu_neg : response u < 0 := by
        rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
        · exact hu_neg
        · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
      intro tau htau_pos
      by_contra htau_notneg
      have htau_nonneg : 0 ≤ response tau := le_of_not_gt htau_notneg
      rcases lt_or_eq_of_le htau_nonneg with hresponse_tau_pos | htau_zero
      · have htau_lt_u : tau < u := by
          by_contra hnot_lt
          rcases lt_or_eq_of_le (le_of_not_gt hnot_lt) with hlt | heq
          · have hanti_lt : response tau < response u :=
              hanti hu_pos htau_pos hlt
            linarith
          · subst tau
            linarith
        have hcontinuous_interval : ContinuousOn response (Set.Icc tau u) :=
          hcontinuous.mono (fun x hx => htau_pos.trans_le hx.1)
        have hzero_between : (0 : Real) ∈ Set.Icc (response u) (response tau) :=
          ⟨le_of_lt hu_neg, le_of_lt hresponse_tau_pos⟩
        rcases intermediate_value_Icc' (le_of_lt htau_lt_u) hcontinuous_interval
            hzero_between with ⟨t, ht, ht_zero⟩
        exact False.elim (hzero ⟨t, htau_pos.trans_le ht.1, ht_zero⟩)
      · exact False.elim (hzero ⟨tau, htau_pos, htau_zero.symm⟩)

/--
A continuous strictly decreasing response always has the source's extended
left-cutoff form.  Its everywhere-negative case is the zero endpoint, hence
the empty policy is already a literal source form in this branch.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_strictAntiOn_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hanti : StrictAntiOn response (Set.Ioi 0)) :
    lemma5SourcePolicyForm .strictlyDecreasing
      (lemma5PositiveResponsePolicy response) := by
  rcases strictAntiOn_positive_or_zero_or_negative_of_continuousOn
      response hcontinuous hanti with hpositive | hzero | hnegative
  · exact
      lemma5SourcePolicyForm_positiveResponse_of_strictAntiOn_positive_or_zero
        response hanti (Or.inl hpositive)
  · exact
      lemma5SourcePolicyForm_positiveResponse_of_strictAntiOn_positive_or_zero
        response hanti (Or.inr hzero)
  · have hpolicy_empty : lemma5PositiveResponsePolicy response = ∅ := by
      ext tau
      constructor
      · intro htau
        rcases htau with ⟨htau_pos, hresponse_pos⟩
        linarith [hnegative tau htau_pos]
      · intro htau
        exact False.elim htau
    refine ⟨(0 : ENNReal), ?_⟩
    simpa [hpolicy_empty]

/--
For a continuous strictly increasing response, the only possibilities are
everywhere positive, a positive zero, or everywhere negative.
-/
theorem strictMonoOn_positive_or_zero_or_negative_of_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hmono : StrictMonoOn response (Set.Ioi 0)) :
    (forall tau : TripLength, 0 < tau -> 0 < response tau) \/
      (exists t : TripLength, 0 < t /\ response t = 0) \/
        (forall tau : TripLength, 0 < tau -> response tau < 0) := by
  by_cases hpositive : forall tau : TripLength, 0 < tau -> 0 < response tau
  · exact Or.inl hpositive
  · push Not at hpositive
    rcases hpositive with ⟨u, hu_pos, hu_nonpos⟩
    by_cases hzero : exists t : TripLength, 0 < t /\ response t = 0
    · exact Or.inr (Or.inl hzero)
    · refine Or.inr (Or.inr ?_)
      have hu_neg : response u < 0 := by
        rcases lt_or_eq_of_le hu_nonpos with hu_neg | hu_zero
        · exact hu_neg
        · exact False.elim (hzero ⟨u, hu_pos, hu_zero⟩)
      intro tau htau_pos
      by_contra htau_notneg
      have htau_nonneg : 0 ≤ response tau := le_of_not_gt htau_notneg
      rcases lt_or_eq_of_le htau_nonneg with hresponse_tau_pos | htau_zero
      · have hu_lt_tau : u < tau := by
          by_contra hnot_lt
          rcases lt_or_eq_of_le (le_of_not_gt hnot_lt) with hlt | heq
          · have hmono_lt : response tau < response u :=
              hmono htau_pos hu_pos hlt
            linarith
          · subst tau
            linarith
        have hcontinuous_interval : ContinuousOn response (Set.Icc u tau) :=
          hcontinuous.mono (fun x hx => hu_pos.trans_le hx.1)
        have hzero_between : (0 : Real) ∈ Set.Icc (response u) (response tau) :=
          ⟨le_of_lt hu_neg, le_of_lt hresponse_tau_pos⟩
        rcases intermediate_value_Icc (le_of_lt hu_lt_tau) hcontinuous_interval
            hzero_between with ⟨t, ht, ht_zero⟩
        exact False.elim (hzero ⟨t, hu_pos.trans_le ht.1, ht_zero⟩)
      · exact False.elim (hzero ⟨tau, htau_pos, htau_zero.symm⟩)

/--
The increasing source table has only finite lower endpoints.  Consequently a
continuous strictly increasing response has either that literal source form or
an empty positive-response policy.  The latter is an explicit repaired branch
rather than a fabricated finite cutoff.
-/
theorem lemma5SourcePolicyForm_or_positiveResponse_empty_of_strictMonoOn_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hmono : StrictMonoOn response (Set.Ioi 0)) :
    lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy response) \/
      lemma5PositiveResponsePolicy response = ∅ := by
  rcases strictMonoOn_positive_or_zero_or_negative_of_continuousOn
      response hcontinuous hmono with hpositive | hzero | hnegative
  · exact Or.inl
      (lemma5SourcePolicyForm_positiveResponse_of_strictMonoOn_positive_or_zero
        response hmono (Or.inl hpositive))
  · exact Or.inl
      (lemma5SourcePolicyForm_positiveResponse_of_strictMonoOn_positive_or_zero
        response hmono (Or.inr hzero))
  · right
    ext tau
    constructor
    · intro htau
      rcases htau with ⟨htau_pos, hresponse_pos⟩
      linarith [hnegative tau htau_pos]
    · intro htau
      exact False.elim htau

/--
The universal decreasing cutoff classification together with the null-boundary
fact used by the a.e. fixed-marginal route.
-/
theorem strictAnti_sourcePolicyForm_and_zeroSetNull_of_continuousOn
    (mu : Measure TripLength) [NoAtoms mu]
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hanti : StrictAntiOn response (Set.Ioi 0)) :
    lemma5SourcePolicyForm .strictlyDecreasing
        (lemma5PositiveResponsePolicy response) /\
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  exact ⟨
    lemma5SourcePolicyForm_positiveResponse_of_strictAntiOn_continuousOn
      response hcontinuous hanti,
    measure_positiveZeroSet_eq_zero_of_strictAnti mu response hanti⟩

/--
The universal increasing classification records the necessary empty-policy
alternative while retaining the nonatomic zero-boundary conclusion.
-/
theorem strictMono_sourcePolicyForm_or_positiveResponse_empty_and_zeroSetNull_of_continuousOn
    (mu : Measure TripLength) [NoAtoms mu]
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hmono : StrictMonoOn response (Set.Ioi 0)) :
    (lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy response) \/
      lemma5PositiveResponsePolicy response = ∅) /\
      mu {tau : TripLength | 0 < tau /\ response tau = 0} = 0 := by
  exact ⟨
    lemma5SourcePolicyForm_or_positiveResponse_empty_of_strictMonoOn_continuousOn
      response hcontinuous hmono,
    measure_positiveZeroSet_eq_zero_of_strictMono mu response hmono⟩

/--
The fixed-marginal optimum, not an endpoint-variation axiom, excludes the
all-negative branch of a strictly increasing normalized response.  The result
therefore has the finite right-cutoff form printed in Lemma 5.
-/
theorem strictMono_sourcePolicyForm_and_zeroSetNull_of_scaled_fixedMarginal_optimal
    (mu : Measure TripLength) [NoAtoms mu]
    (base marginal : TripLength -> Real) (sigma : TripPolicy)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass mu sigma)
    (hmarginal_integrable : IntegrableOn marginal acceptAllPolicy mu)
    (hoptimal :
      forall sigma' : TripPolicy, sigma' ⊆ acceptAllPolicy ->
        MeasurableSet sigma' ->
          lemma5MarginalSetReward mu marginal sigma' <=
            lemma5MarginalSetReward mu marginal sigma)
    (hnegative_transfer :
      forall tau : TripLength, 0 < tau -> base tau < 0 -> marginal tau < 0)
    (hcontinuous : ContinuousOn base (Set.Ioi 0))
    (hmono : StrictMonoOn base (Set.Ioi 0)) :
    lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy base) /\
      mu {tau : TripLength | 0 < tau /\ base tau = 0} = 0 := by
  have hpositive_or_zero :
      (forall tau : TripLength, 0 < tau -> 0 < base tau) \/
        exists t : TripLength, 0 < t /\ base t = 0 :=
    lemma5BasePositive_or_zero_of_strictMonoOn_scaled_marginal_optimal
      mu base marginal sigma hsigma_measurable hsigma_subset hmass
      hmarginal_integrable hoptimal hnegative_transfer hcontinuous hmono
  exact ⟨
    lemma5SourcePolicyForm_positiveResponse_of_strictMonoOn_positive_or_zero
      base hmono hpositive_or_zero,
    measure_positiveZeroSet_eq_zero_of_strictMono mu base hmono⟩

/--
The decreasing counterpart of
`strictMono_sourcePolicyForm_and_zeroSetNull_of_scaled_fixedMarginal_optimal`.
The all-positive branch is represented by the source's infinity endpoint.
-/
theorem strictAnti_sourcePolicyForm_and_zeroSetNull_of_scaled_fixedMarginal_optimal
    (mu : Measure TripLength) [NoAtoms mu]
    (base marginal : TripLength -> Real) (sigma : TripPolicy)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass mu sigma)
    (hmarginal_integrable : IntegrableOn marginal acceptAllPolicy mu)
    (hoptimal :
      forall sigma' : TripPolicy, sigma' ⊆ acceptAllPolicy ->
        MeasurableSet sigma' ->
          lemma5MarginalSetReward mu marginal sigma' <=
            lemma5MarginalSetReward mu marginal sigma)
    (hnegative_transfer :
      forall tau : TripLength, 0 < tau -> base tau < 0 -> marginal tau < 0)
    (hcontinuous : ContinuousOn base (Set.Ioi 0))
    (hanti : StrictAntiOn base (Set.Ioi 0)) :
    lemma5SourcePolicyForm .strictlyDecreasing
        (lemma5PositiveResponsePolicy base) /\
      mu {tau : TripLength | 0 < tau /\ base tau = 0} = 0 := by
  have hpositive_or_zero :
      (forall tau : TripLength, 0 < tau -> 0 < base tau) \/
        exists t : TripLength, 0 < t /\ base t = 0 :=
    lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_optimal
      mu base marginal sigma hsigma_measurable hsigma_subset hmass
      hmarginal_integrable hoptimal hnegative_transfer hcontinuous hanti
  exact ⟨
    lemma5SourcePolicyForm_positiveResponse_of_strictAntiOn_positive_or_zero
      base hanti hpositive_or_zero,
    measure_positiveZeroSet_eq_zero_of_strictAnti mu base hanti⟩

/--
The increasing fixed-marginal cutoff conclusion under the exact comparison it
uses.  In the dynamic proof this comparison is supplied by evaluating open
optimality at the empty policy; no arbitrary replacement-policy premise is
needed here.
-/
theorem strictMono_sourcePolicyForm_and_zeroSetNull_of_scaled_emptyComparison
    (mu : Measure TripLength) [NoAtoms mu]
    (base marginal : TripLength -> Real) (sigma : TripPolicy)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass mu sigma)
    (hmarginal_integrable : IntegrableOn marginal acceptAllPolicy mu)
    (hempty_comparison :
      lemma5MarginalSetReward mu marginal ∅ <=
        lemma5MarginalSetReward mu marginal sigma)
    (hnegative_transfer :
      forall tau : TripLength, 0 < tau -> base tau < 0 -> marginal tau < 0)
    (hcontinuous : ContinuousOn base (Set.Ioi 0))
    (hmono : StrictMonoOn base (Set.Ioi 0)) :
    lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy base) /\
      mu {tau : TripLength | 0 < tau /\ base tau = 0} = 0 := by
  have hpositive_or_zero :
      (forall tau : TripLength, 0 < tau -> 0 < base tau) \/
        exists t : TripLength, 0 < t /\ base t = 0 :=
    lemma5BasePositive_or_zero_of_strictMonoOn_scaled_marginal_emptyComparison
      mu base marginal sigma hsigma_measurable hsigma_subset hmass
      hmarginal_integrable hempty_comparison hnegative_transfer hcontinuous hmono
  exact ⟨
    lemma5SourcePolicyForm_positiveResponse_of_strictMonoOn_positive_or_zero
      base hmono hpositive_or_zero,
    measure_positiveZeroSet_eq_zero_of_strictMono mu base hmono⟩

/--
The decreasing counterpart of
`strictMono_sourcePolicyForm_and_zeroSetNull_of_scaled_emptyComparison`.
-/
theorem strictAnti_sourcePolicyForm_and_zeroSetNull_of_scaled_emptyComparison
    (mu : Measure TripLength) [NoAtoms mu]
    (base marginal : TripLength -> Real) (sigma : TripPolicy)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass mu sigma)
    (hmarginal_integrable : IntegrableOn marginal acceptAllPolicy mu)
    (hempty_comparison :
      lemma5MarginalSetReward mu marginal ∅ <=
        lemma5MarginalSetReward mu marginal sigma)
    (hnegative_transfer :
      forall tau : TripLength, 0 < tau -> base tau < 0 -> marginal tau < 0)
    (hcontinuous : ContinuousOn base (Set.Ioi 0))
    (hanti : StrictAntiOn base (Set.Ioi 0)) :
    lemma5SourcePolicyForm .strictlyDecreasing
        (lemma5PositiveResponsePolicy base) /\
      mu {tau : TripLength | 0 < tau /\ base tau = 0} = 0 := by
  have hpositive_or_zero :
      (forall tau : TripLength, 0 < tau -> 0 < base tau) \/
        exists t : TripLength, 0 < t /\ base t = 0 :=
    lemma5BasePositive_or_zero_of_strictAntiOn_scaled_marginal_emptyComparison
      mu base marginal sigma hsigma_measurable hsigma_subset hmass
      hmarginal_integrable hempty_comparison hnegative_transfer hcontinuous hanti
  exact ⟨
    lemma5SourcePolicyForm_positiveResponse_of_strictAntiOn_positive_or_zero
      base hanti hpositive_or_zero,
    measure_positiveZeroSet_eq_zero_of_strictAnti mu base hanti⟩

/--
An open order-connected feasible policy set is exactly one extended middle
interval.  This elementary order-topology result is what accounts for the
source's zero and infinity endpoints without any endpoint-derivative path.
-/
theorem exists_extendedMiddlePolicy_eq_of_isOpen_ordConnected
    (policy : TripPolicy)
    (hpolicy_subset : policy ⊆ acceptAllPolicy)
    (hpolicy_open : IsOpen policy)
    (hpolicy_connected : policy.OrdConnected) :
    exists lower upper : ENNReal,
      policy = gn21ExtendedMiddlePolicy lower upper := by
  classical
  by_cases hpolicy_nonempty : policy.Nonempty
  · have hpolicy_bddBelow : BddBelow policy := by
      refine ⟨0, ?_⟩
      intro tau htau
      exact le_of_lt (hpolicy_subset htau)
    have hinf_nonneg : 0 <= sInf policy := by
      apply le_csInf hpolicy_nonempty
      intro tau htau
      exact le_of_lt (hpolicy_subset htau)
    let lower : NNReal := ⟨sInf policy, hinf_nonneg⟩
    have hinf_lt_of_mem :
        forall {tau : TripLength}, tau ∈ policy -> sInf policy < tau := by
      intro tau htau
      by_contra hnot_lt
      have htau_le_inf : tau <= sInf policy := le_of_not_gt hnot_lt
      rcases mem_nhds_iff_exists_Ioo_subset.mp (hpolicy_open.mem_nhds htau) with
        ⟨left, right, htau_interval, hinterval_subset⟩
      rcases exists_between htau_interval.1 with ⟨inside, hleft_inside, hinside_tau⟩
      have hinside_mem : inside ∈ policy :=
        hinterval_subset ⟨hleft_inside, hinside_tau.trans htau_interval.2⟩
      have hinf_le_inside : sInf policy <= inside :=
        csInf_le hpolicy_bddBelow hinside_mem
      linarith
    by_cases hpolicy_bddAbove : BddAbove policy
    · have hsup_nonneg : 0 <= sSup policy := by
        rcases hpolicy_nonempty with ⟨tau, htau⟩
        exact (le_of_lt (hpolicy_subset htau)).trans
          (le_csSup hpolicy_bddAbove htau)
      let upper : NNReal := ⟨sSup policy, hsup_nonneg⟩
      have hmem_lt_sup :
          forall {tau : TripLength}, tau ∈ policy -> tau < sSup policy := by
        intro tau htau
        by_contra hnot_lt
        have hsup_le_tau : sSup policy <= tau := le_of_not_gt hnot_lt
        rcases mem_nhds_iff_exists_Ioo_subset.mp (hpolicy_open.mem_nhds htau) with
          ⟨left, right, htau_interval, hinterval_subset⟩
        rcases exists_between htau_interval.2 with ⟨inside, htau_inside, hinside_right⟩
        have hinside_mem : inside ∈ policy :=
          hinterval_subset ⟨htau_interval.1.trans htau_inside, hinside_right⟩
        have hinside_le_sup : inside <= sSup policy :=
          le_csSup hpolicy_bddAbove hinside_mem
        linarith
      have hpolicy_eq_interval : policy = Set.Ioo (sInf policy) (sSup policy) := by
        ext tau
        constructor
        · intro htau
          exact ⟨hinf_lt_of_mem htau, hmem_lt_sup htau⟩
        · intro htau
          have hbelow : ∃ left, left ∈ policy ∧ left < tau := by
            by_contra hnot
            have htau_le_all : forall left : TripLength, left ∈ policy -> tau <= left := by
              intro left hleft
              exact le_of_not_gt (by
                intro hleft_tau
                exact hnot ⟨left, hleft, hleft_tau⟩)
            have htau_le_inf : tau <= sInf policy :=
              le_csInf hpolicy_nonempty htau_le_all
            exact (not_lt_of_ge htau_le_inf) htau.1
          have habove : ∃ right, right ∈ policy ∧ tau < right := by
            by_contra hnot
            have hall_le_tau : forall right : TripLength, right ∈ policy -> right <= tau := by
              intro right hright
              exact le_of_not_gt (by
                intro htau_right
                exact hnot ⟨right, hright, htau_right⟩)
            have hsup_le_tau : sSup policy <= tau :=
              csSup_le hpolicy_nonempty hall_le_tau
            exact (not_lt_of_ge hsup_le_tau) htau.2
          rcases hbelow with ⟨left, hleft_mem, hleft_tau⟩
          rcases habove with ⟨right, hright_mem, htau_right⟩
          exact hpolicy_connected.out hleft_mem hright_mem
            ⟨le_of_lt hleft_tau, le_of_lt htau_right⟩
      refine ⟨(lower : ENNReal), (upper : ENNReal), ?_⟩
      rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo]
      simpa only [lower, upper] using hpolicy_eq_interval
    · have hpolicy_eq_ray : policy = Set.Ioi (sInf policy) := by
        ext tau
        constructor
        · exact hinf_lt_of_mem
        · intro htau
          have hbelow : ∃ left, left ∈ policy ∧ left < tau := by
            by_contra hnot
            have htau_le_all : forall left : TripLength, left ∈ policy -> tau <= left := by
              intro left hleft
              exact le_of_not_gt (by
                intro hleft_tau
                exact hnot ⟨left, hleft, hleft_tau⟩)
            have htau_le_inf : tau <= sInf policy :=
              le_csInf hpolicy_nonempty htau_le_all
            exact (not_lt_of_ge htau_le_inf) htau
          rcases (not_bddAbove_iff.mp hpolicy_bddAbove) tau with
            ⟨right, hright_mem, htau_right⟩
          rcases hbelow with ⟨left, hleft_mem, hleft_tau⟩
          exact hpolicy_connected.out hleft_mem hright_mem
            ⟨le_of_lt hleft_tau, le_of_lt htau_right⟩
      refine ⟨(lower : ENNReal), (⊤ : ENNReal), ?_⟩
      rw [gn21ExtendedMiddlePolicy_coe_top_eq_Ioi]
      simpa only [lower] using hpolicy_eq_ray
  · have hpolicy_empty : policy = ∅ := Set.not_nonempty_iff_eq_empty.mp hpolicy_nonempty
    refine ⟨0, 0, ?_⟩
    rw [hpolicy_empty]
    exact (gn21ExtendedMiddlePolicy_eq_empty_of_le le_rfl).symm

/-- A response continuous on positive trip lengths has an open positive-response policy. -/
theorem isOpen_lemma5PositiveResponsePolicy_of_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0)) :
    IsOpen (lemma5PositiveResponsePolicy response) := by
  change IsOpen (Set.Ioi 0 ∩ response ⁻¹' Set.Ioi 0)
  exact hcontinuous.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi

/-- Strict quasi-concavity makes the positive-response policy order-connected. -/
theorem ordConnected_lemma5PositiveResponsePolicy_of_strictQuasiConcave
    (response : TripLength -> Real)
    (hquasi : strictQuasiConcaveOnPositive response) :
    (lemma5PositiveResponsePolicy response).OrdConnected := by
  apply Set.ordConnected_of_Ioo
  intro left hleft right hright hleft_right point hpoint
  refine ⟨lt_trans hleft.1 hpoint.1, ?_⟩
  have hstrict :=
    AppliedModelingLib.StrictQuasiConcaveOnPositive.lt_between hquasi
      hleft.1 hpoint.1 hpoint.2
  exact lt_trans (lt_min hleft.2 hright.2) hstrict

/--
Strict quasi-concavity and continuity on positive lengths give the exact
source middle-interval positive-response form, including the empty and
unbounded cases.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_strictQuasiConcave_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hquasi : strictQuasiConcaveOnPositive response) :
    lemma5SourcePolicyForm .strictlyQuasiConcave
      (lemma5PositiveResponsePolicy response) := by
  exact exists_extendedMiddlePolicy_eq_of_isOpen_ordConnected
    (lemma5PositiveResponsePolicy response)
    (lemma5PositiveResponsePolicy_subset_acceptAll response)
    (isOpen_lemma5PositiveResponsePolicy_of_continuousOn response hcontinuous)
    (ordConnected_lemma5PositiveResponsePolicy_of_strictQuasiConcave
      response hquasi)

/-- Strict quasi-convexity makes the nonpositive-response policy order-connected. -/
theorem ordConnected_lemma5NonpositiveResponsePolicy_of_strictQuasiConvex
    (response : TripLength -> Real)
    (hquasi : strictQuasiConvexOnPositive response) :
    {tau : TripLength | 0 < tau ∧ response tau ≤ 0}.OrdConnected := by
  apply Set.ordConnected_of_Ioo
  intro left hleft right hright hleft_right point hpoint
  refine ⟨lt_trans hleft.1 hpoint.1, ?_⟩
  have hstrict :=
    AppliedModelingLib.StrictQuasiConvexOnPositive.lt_of_between hquasi
      hleft.1 hpoint.1 hpoint.2
  exact le_trans (le_of_lt hstrict) (max_le hleft.2 hright.2)

/--
Continuity on positive lengths makes the nonpositive-response set closed after
adjoining the feasible zero endpoint.  This is the precise topological fact
needed to retain finite cutoff boundaries without assuming their signs.
-/
theorem isClosed_zeroUnion_lemma5NonpositiveResponsePolicy_of_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0)) :
    IsClosed ({0} ∪ {tau : TripLength | 0 < tau ∧ response tau ≤ 0}) := by
  rcases continuousOn_iff_isClosed.mp hcontinuous (Set.Iic 0) isClosed_Iic with
    ⟨u, hu_closed, hu_eq⟩
  have hset_eq :
      ({0} ∪ {tau : TripLength | 0 < tau ∧ response tau ≤ 0}) =
        {0} ∪ (u ∩ Set.Ici 0) := by
    ext tau
    by_cases htau_zero : tau = 0
    · subst tau
      simp
    · constructor
      · intro htau
        rcases htau with htau | htau
        · exact False.elim (htau_zero (Set.mem_singleton_iff.mp htau))
        · right
          have htau_u : tau ∈ u := by
            have htau_preimage : tau ∈ response ⁻¹' Set.Iic 0 ∩ Set.Ioi 0 :=
              ⟨htau.2, htau.1⟩
            rw [hu_eq] at htau_preimage
            exact htau_preimage.1
          exact ⟨htau_u, le_of_lt htau.1⟩
      · intro htau
        rcases htau with htau | htau
        · exact False.elim (htau_zero (Set.mem_singleton_iff.mp htau))
        · have htau_preimage : tau ∈ response ⁻¹' Set.Iic 0 ∩ Set.Ioi 0 := by
            rw [hu_eq]
            exact ⟨htau.1, lt_of_le_of_ne htau.2 (Ne.symm htau_zero)⟩
          exact Or.inr ⟨htau_preimage.2, htau_preimage.1⟩
  rw [hset_eq]
  exact isClosed_singleton.union (hu_closed.inter isClosed_Ici)

/--
A continuous strictly quasi-convex response has an endpoint-complete positive
set of the source's two-tail form.  The proof works with the actual
nonpositive set: its infimum and supremum are used only when finite, and the
zero and infinity cases are discharged explicitly.
-/
theorem exists_extendedTwoTailPolicy_eq_of_strictQuasiConvex_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hquasi : strictQuasiConvexOnPositive response) :
    ∃ lower upper : ENNReal,
      lemma5PositiveResponsePolicy response =
        gn21ExtendedTwoTailPolicy lower upper := by
  let negativePolicy : Set TripLength :=
    {tau : TripLength | 0 < tau ∧ response tau ≤ 0}
  have hnegative_connected : negativePolicy.OrdConnected := by
    simpa only [negativePolicy] using
      ordConnected_lemma5NonpositiveResponsePolicy_of_strictQuasiConvex
        response hquasi
  have hnegative_bddBelow : BddBelow negativePolicy := by
    refine ⟨0, ?_⟩
    intro tau htau
    exact le_of_lt htau.1
  have hnegative_closed_completion :
      IsClosed ({0} ∪ negativePolicy) := by
    simpa only [negativePolicy] using
      isClosed_zeroUnion_lemma5NonpositiveResponsePolicy_of_continuousOn
        response hcontinuous
  have hpositive_iff_not_negative :
      ∀ {tau : TripLength}, 0 < tau ->
        (tau ∈ lemma5PositiveResponsePolicy response ↔ tau ∉ negativePolicy) := by
    intro tau htau
    constructor
    · intro htau_positive htau_negative
      exact (not_lt_of_ge htau_negative.2) htau_positive.2
    · intro htau_not_negative
      refine ⟨htau, ?_⟩
      exact lt_of_not_ge fun htau_nonpositive =>
        htau_not_negative ⟨htau, htau_nonpositive⟩
  by_cases hnegative_nonempty : negativePolicy.Nonempty
  · have hclosure_subset : closure negativePolicy ⊆ {0} ∪ negativePolicy :=
      closure_minimal (fun tau htau => Or.inr htau) hnegative_closed_completion
    have hinf_nonneg : 0 ≤ sInf negativePolicy := by
      apply le_csInf hnegative_nonempty
      intro tau htau
      exact le_of_lt htau.1
    have hinf_mem_completion : sInf negativePolicy ∈ {0} ∪ negativePolicy :=
      hclosure_subset (csInf_mem_closure hnegative_nonempty hnegative_bddBelow)
    by_cases hnegative_bddAbove : BddAbove negativePolicy
    · have hsup_mem_completion : sSup negativePolicy ∈ {0} ∪ negativePolicy :=
        hclosure_subset (csSup_mem_closure hnegative_nonempty hnegative_bddAbove)
      have hsup_pos : 0 < sSup negativePolicy := by
        rcases hnegative_nonempty with ⟨tau, htau⟩
        exact lt_of_lt_of_le htau.1 (le_csSup hnegative_bddAbove htau)
      have hsup_mem : sSup negativePolicy ∈ negativePolicy := by
        rcases hsup_mem_completion with hsup_zero | hsup_negative
        · exact False.elim (ne_of_gt hsup_pos (Set.mem_singleton_iff.mp hsup_zero))
        · exact hsup_negative
      by_cases hinf_zero : sInf negativePolicy = 0
      · have hpositive_eq :
            lemma5PositiveResponsePolicy response = Set.Ioi (sSup negativePolicy) := by
          ext tau
          constructor
          · intro htau
            by_contra hnot_lt
            have htau_le_sup : tau ≤ sSup negativePolicy := le_of_not_gt hnot_lt
            have htau_negative : tau ∈ negativePolicy := by
              rcases eq_or_lt_of_le htau_le_sup with htau_eq_sup | htau_lt_sup
              · simpa only [htau_eq_sup] using hsup_mem
              · have hinf_lt_tau : sInf negativePolicy < tau := by
                  rw [hinf_zero]
                  exact htau.1
                rcases (isGLB_lt_iff
                    (isGLB_csInf hnegative_nonempty hnegative_bddBelow)).mp
                    hinf_lt_tau with
                  ⟨left, hleft_negative, hleft_lt_tau⟩
                exact hnegative_connected.out hleft_negative hsup_mem
                  ⟨le_of_lt hleft_lt_tau, le_of_lt htau_lt_sup⟩
            exact (not_lt_of_ge htau_negative.2) htau.2
          · intro htau
            exact (hpositive_iff_not_negative (lt_trans hsup_pos htau)).mpr (by
              intro htau_negative
              exact (not_lt_of_ge (le_csSup hnegative_bddAbove htau_negative)) htau)
        let upper : NNReal := ⟨sSup negativePolicy, le_of_lt hsup_pos⟩
        refine ⟨0, (upper : ENNReal), ?_⟩
        rw [gn21ExtendedTwoTailPolicy_zero_coe_eq_Ioi]
        simpa only [upper] using hpositive_eq
      · have hinf_pos : 0 < sInf negativePolicy :=
          lt_of_le_of_ne hinf_nonneg (Ne.symm hinf_zero)
        have hinf_mem : sInf negativePolicy ∈ negativePolicy := by
          rcases hinf_mem_completion with hinf_zero_mem | hinf_negative
          · exact False.elim (hinf_zero (Set.mem_singleton_iff.mp hinf_zero_mem))
          · exact hinf_negative
        have hpositive_eq :
            lemma5PositiveResponsePolicy response =
              Set.Ioo 0 (sInf negativePolicy) ∪ Set.Ioi (sSup negativePolicy) := by
          ext tau
          constructor
          · intro htau
            by_cases htau_lt_inf : tau < sInf negativePolicy
            · exact Or.inl ⟨htau.1, htau_lt_inf⟩
            · right
              by_contra hnot_lt_sup
              have hinf_le_tau : sInf negativePolicy ≤ tau := le_of_not_gt htau_lt_inf
              have htau_le_sup : tau ≤ sSup negativePolicy := le_of_not_gt hnot_lt_sup
              have htau_negative : tau ∈ negativePolicy :=
                hnegative_connected.out hinf_mem hsup_mem ⟨hinf_le_tau, htau_le_sup⟩
              exact (not_lt_of_ge htau_negative.2) htau.2
          · intro htau
            rcases htau with htau | htau
            · exact (hpositive_iff_not_negative htau.1).mpr (by
                intro htau_negative
                exact (not_lt_of_ge
                  (csInf_le hnegative_bddBelow htau_negative)) htau.2)
            · exact (hpositive_iff_not_negative
                (lt_trans hsup_pos htau)).mpr (by
                  intro htau_negative
                  exact (not_lt_of_ge
                    (le_csSup hnegative_bddAbove htau_negative)) htau)
        let lower : NNReal := ⟨sInf negativePolicy, hinf_nonneg⟩
        let upper : NNReal := ⟨sSup negativePolicy, le_of_lt hsup_pos⟩
        refine ⟨(lower : ENNReal), (upper : ENNReal), ?_⟩
        rw [gn21ExtendedTwoTailPolicy_coe_coe_eq_Ioo_union_Ioi]
        simpa only [lower, upper] using hpositive_eq
    · by_cases hinf_zero : sInf negativePolicy = 0
      · have hpositive_empty : lemma5PositiveResponsePolicy response = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          intro hpositive_nonempty
          rcases hpositive_nonempty with ⟨tau, htau⟩
          have hinf_lt_tau : sInf negativePolicy < tau := by
            rw [hinf_zero]
            exact htau.1
          rcases (isGLB_lt_iff
              (isGLB_csInf hnegative_nonempty hnegative_bddBelow)).mp
              hinf_lt_tau with
            ⟨left, hleft_negative, hleft_lt_tau⟩
          rcases (not_bddAbove_iff.mp hnegative_bddAbove) tau with
            ⟨right, hright_negative, htau_lt_right⟩
          have htau_negative : tau ∈ negativePolicy :=
            hnegative_connected.out hleft_negative hright_negative
              ⟨le_of_lt hleft_lt_tau, le_of_lt htau_lt_right⟩
          exact (not_lt_of_ge htau_negative.2) htau.2
        refine ⟨0, (⊤ : ENNReal), ?_⟩
        rw [gn21ExtendedTwoTailPolicy_zero_top]
        exact hpositive_empty
      · have hinf_pos : 0 < sInf negativePolicy :=
          lt_of_le_of_ne hinf_nonneg (Ne.symm hinf_zero)
        have hinf_mem : sInf negativePolicy ∈ negativePolicy := by
          rcases hinf_mem_completion with hinf_zero_mem | hinf_negative
          · exact False.elim (hinf_zero (Set.mem_singleton_iff.mp hinf_zero_mem))
          · exact hinf_negative
        have hpositive_eq :
            lemma5PositiveResponsePolicy response = Set.Ioo 0 (sInf negativePolicy) := by
          ext tau
          constructor
          · intro htau
            refine ⟨htau.1, ?_⟩
            by_contra hnot_lt_inf
            have hinf_le_tau : sInf negativePolicy ≤ tau := le_of_not_gt hnot_lt_inf
            rcases (not_bddAbove_iff.mp hnegative_bddAbove) tau with
              ⟨right, hright_negative, htau_lt_right⟩
            have htau_negative : tau ∈ negativePolicy :=
              hnegative_connected.out hinf_mem hright_negative
                ⟨hinf_le_tau, le_of_lt htau_lt_right⟩
            exact (not_lt_of_ge htau_negative.2) htau.2
          · intro htau
            exact (hpositive_iff_not_negative htau.1).mpr (by
              intro htau_negative
              exact (not_lt_of_ge
                (csInf_le hnegative_bddBelow htau_negative)) htau.2)
        let lower : NNReal := ⟨sInf negativePolicy, hinf_nonneg⟩
        refine ⟨(lower : ENNReal), (⊤ : ENNReal), ?_⟩
        rw [gn21ExtendedTwoTailPolicy_coe_top_eq_Ioo]
        simpa only [lower] using hpositive_eq
  · have hnegative_empty : negativePolicy = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnegative_nonempty
    refine ⟨(⊤ : ENNReal), 0, ?_⟩
    rw [gn21ExtendedTwoTailPolicy_top_left]
    ext tau
    constructor
    · intro htau
      exact htau.1
    · intro htau
      exact (hpositive_iff_not_negative htau).mpr (by simp [hnegative_empty])

/--
Strict quasi-convexity and continuity on positive lengths give the exact
source two-tail form, with explicit finite, zero, and infinity endpoint
handling.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_strictQuasiConvex_continuousOn
    (response : TripLength -> Real)
    (hcontinuous : ContinuousOn response (Set.Ioi 0))
    (hquasi : strictQuasiConvexOnPositive response) :
    lemma5SourcePolicyForm .strictlyQuasiConvex
      (lemma5PositiveResponsePolicy response) := by
  rcases exists_extendedTwoTailPolicy_eq_of_strictQuasiConvex_continuousOn
      response hcontinuous hquasi with
    ⟨lower, upper, hpositive_eq⟩
  exact ⟨lower, upper, hpositive_eq⟩

/-- The affine normalized CTMC Lemma 6 response is continuous on positive trip lengths. -/
theorem continuousOn_affine_gn21Lemma6Response_ctmc
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : Real) :
    ContinuousOn
      (fun tau : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
          (m * tau + a) Qi Qj Ti Tj Ri Rj)
      (Set.Ioi 0) := by
  have hswitch :
      ContinuousOn (fun tau : TripLength => gn21SwitchProb lambdaIJ lambdaJI tau)
        (Set.Ioi 0) :=
    (continuous_gn21SwitchProb lambdaIJ lambdaJI).continuousOn
  have hid : ContinuousOn (fun tau : TripLength => tau) (Set.Ioi 0) :=
    continuous_id.continuousOn
  have hne : ∀ tau ∈ Set.Ioi (0 : Real), tau ≠ 0 := by
    intro tau htau
    exact ne_of_gt htau
  unfold gn21Lemma6Response
  exact
    (((hswitch.div hid hne).mul continuousOn_const).add
        ((((continuousOn_const.mul hid).add continuousOn_const).div hid hne).mul
          continuousOn_const)).sub continuousOn_const

/--
After substituting an affine price, the normalized Lemma 6 response is a
constant plus a linear combination of `q(u) / u` and `1 / u`.
-/
theorem affine_gn21Lemma6Response_per_time_form
    (q u m a Qi Qj Ti Tj Ri Rj : Real)
    (hu : u ≠ 0) :
    gn21Lemma6Response q u (m * u + a) Qi Qj Ti Tj Ri Rj =
      (Rj - Ri) * (q / u) +
          (a * (Qi / Ti + Qj / Tj)) * (1 / u) +
        (m * (Qi / Ti + Qj / Tj) -
          (Qi / Ti * Rj + Qj / Tj * Ri)) := by
  unfold gn21Lemma6Response
  field_simp [hu]
  ring

/--
Nonnegative coefficients on the two strictly decreasing affine response
components give a strictly decreasing normalized response when one coefficient
is positive.
-/
theorem strictAntiOn_affine_gn21Lemma6Response_ctmc
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : Real)
    (hgap_nonneg : 0 <= Rj - Ri)
    (hintercept_nonneg : 0 <= a * (Qi / Ti + Qj / Tj))
    (hstrict :
      0 < Rj - Ri \/ 0 < a * (Qi / Ti + Qj / Tj))
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI) :
    StrictAntiOn
      (fun tau : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
          (m * tau + a) Qi Qj Ti Tj Ri Rj)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hswitch_anti :=
    paper_remark1_switch_probability_per_time_strictAntiOn
      lambdaIJ lambdaJI hlambdaIJ hsum
  have hswitch :
      gn21SwitchProb lambdaIJ lambdaJI y / y <
        gn21SwitchProb lambdaIJ lambdaJI x / x :=
    hswitch_anti hx hy hxy
  have hinv : 1 / y < 1 / x :=
    one_div_strictAntiOn hx hy hxy
  change
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI y) y
        (m * y + a) Qi Qj Ti Tj Ri Rj <
      gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI x) x
        (m * x + a) Qi Qj Ti Tj Ri Rj
  rw [
    affine_gn21Lemma6Response_per_time_form
      (gn21SwitchProb lambdaIJ lambdaJI y) y m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hy),
    affine_gn21Lemma6Response_per_time_form
      (gn21SwitchProb lambdaIJ lambdaJI x) x m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hx)]
  rcases hstrict with hgap_pos | hintercept_pos
  · have hfirst :
        (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI y / y) <
          (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI x / x) :=
      mul_lt_mul_of_pos_left hswitch hgap_pos
    have hsecond :
        a * (Qi / Ti + Qj / Tj) * (1 / y) <=
          a * (Qi / Ti + Qj / Tj) * (1 / x) :=
      mul_le_mul_of_nonneg_left (le_of_lt hinv) hintercept_nonneg
    linarith
  · have hfirst :
        (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI y / y) <=
          (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI x / x) :=
      mul_le_mul_of_nonneg_left (le_of_lt hswitch) hgap_nonneg
    have hsecond :
        a * (Qi / Ti + Qj / Tj) * (1 / y) <
          a * (Qi / Ti + Qj / Tj) * (1 / x) :=
      mul_lt_mul_of_pos_left hinv hintercept_pos
    linarith

/--
Nonpositive coefficients on the two strictly decreasing affine response
components give a strictly increasing normalized response when one coefficient
is negative.
-/
theorem strictMonoOn_affine_gn21Lemma6Response_ctmc
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : Real)
    (hgap_nonpos : Rj - Ri <= 0)
    (hintercept_nonpos : a * (Qi / Ti + Qj / Tj) <= 0)
    (hstrict :
      Rj - Ri < 0 \/ a * (Qi / Ti + Qj / Tj) < 0)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI) :
    StrictMonoOn
      (fun tau : TripLength =>
        gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
          (m * tau + a) Qi Qj Ti Tj Ri Rj)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hswitch_anti :=
    paper_remark1_switch_probability_per_time_strictAntiOn
      lambdaIJ lambdaJI hlambdaIJ hsum
  have hswitch :
      gn21SwitchProb lambdaIJ lambdaJI y / y <
        gn21SwitchProb lambdaIJ lambdaJI x / x :=
    hswitch_anti hx hy hxy
  have hinv : 1 / y < 1 / x :=
    one_div_strictAntiOn hx hy hxy
  change
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI x) x
        (m * x + a) Qi Qj Ti Tj Ri Rj <
      gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI y) y
        (m * y + a) Qi Qj Ti Tj Ri Rj
  rw [
    affine_gn21Lemma6Response_per_time_form
      (gn21SwitchProb lambdaIJ lambdaJI x) x m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hx),
    affine_gn21Lemma6Response_per_time_form
      (gn21SwitchProb lambdaIJ lambdaJI y) y m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hy)]
  rcases hstrict with hgap_neg | hintercept_neg
  · have hfirst :
        (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI x / x) <
          (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI y / y) :=
      mul_lt_mul_of_neg_left hswitch hgap_neg
    have hsecond :
        a * (Qi / Ti + Qj / Tj) * (1 / x) <=
          a * (Qi / Ti + Qj / Tj) * (1 / y) :=
      mul_le_mul_of_nonpos_left (le_of_lt hinv) hintercept_nonpos
    linarith
  · have hfirst :
        (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI x / x) <=
          (Rj - Ri) * (gn21SwitchProb lambdaIJ lambdaJI y / y) :=
      mul_le_mul_of_nonpos_left (le_of_lt hswitch) hgap_nonpos
    have hsecond :
        a * (Qi / Ti + Qj / Tj) * (1 / x) <
          a * (Qi / Ti + Qj / Tj) * (1 / y) :=
      mul_lt_mul_of_neg_left hinv hintercept_neg
    linarith

/--
At a strictly ordered state pair, a non-surge affine price with nonnegative
intercept has a strictly decreasing normalized Lemma 6 response.
-/
theorem strictAntiOn_gn21MeasuredLeft_positiveAffineLemma6Response
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (sigmaI sigmaJ : TripPolicy)
    (hRi_lt_Rj : Ri < Rj)
    (ha_nonneg : 0 <= a)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI) :
    StrictAntiOn
      (gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
        switchIJ switchJI (affinePricing m a) sigmaI sigmaJ Ri Rj)
      (Set.Ioi 0) := by
  have hintercept_nonneg :
      0 <= a *
        (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ) :=
    mul_nonneg ha_nonneg (le_of_lt hstate_weight_pos)
  simpa [gn21MeasuredLeftLemma6ResponseAtCurrent, affinePricing] using
    (strictAntiOn_affine_gn21Lemma6Response_ctmc
      m a
      (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
      (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
      (gn21ScaledStateTime muI arrivalI sigmaI)
      (gn21ScaledStateTime muJ arrivalJ sigmaJ)
      Ri Rj switchIJ switchJI
      (by linarith) hintercept_nonneg (Or.inl (by linarith))
      hswitchIJ_pos hsum)

/--
At a strictly ordered state pair, a surge affine price `m*u-a` with
nonnegative `a` has a strictly increasing normalized Lemma 6 response.
-/
theorem strictMonoOn_gn21MeasuredRight_negativeAffineLemma6Response
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (sigmaI sigmaJ : TripPolicy)
    (hRi_lt_Rj : Ri < Rj)
    (ha_nonneg : 0 <= a)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hswitchJI_pos : 0 < switchJI)
    (hsum : 0 < switchJI + switchIJ) :
    StrictMonoOn
      (gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
        switchIJ switchJI (affinePricing m (-a)) sigmaI sigmaJ Ri Rj)
      (Set.Ioi 0) := by
  have hintercept_nonpos :
      (-a) *
        (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI) <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha_nonneg)
      (le_of_lt hstate_weight_pos)
  simpa [gn21MeasuredRightLemma6ResponseAtCurrent, affinePricing, add_comm,
    add_left_comm, add_assoc] using
    (strictMonoOn_affine_gn21Lemma6Response_ctmc
      m (-a)
      (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
      (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
      (gn21ScaledStateTime muJ arrivalJ sigmaJ)
      (gn21ScaledStateTime muI arrivalI sigmaI)
      Rj Ri switchJI switchIJ
      (by linarith) hintercept_nonpos (Or.inl (by linarith))
      hswitchJI_pos hsum)

/--
The non-surge affine-plus branch transferred to the actual Appendix-D
marginal response.  The decreasing source family already represents its empty
endpoint, so this result is valid for every feasible fixed policy satisfying
the source rate order.
-/
theorem gn21MeasuredLeft_positiveAffineMarginal_sourceLeftForm_and_zeroSetNull
    (muI muJ : Measure TripLength) [NoAtoms muI]
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (wJ : PricingFunction)
    (sigmaI sigmaJ : TripPolicy)
    (hRi_lt_Rj : Ri < Rj)
    (ha_nonneg : 0 <= a)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hQj_pos :
      0 < gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI (affinePricing m a) sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    lemma5SourcePolicyForm .strictlyDecreasing
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI (affinePricing m a) wJ sigmaI sigmaJ)) /\
      muI
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI (affinePricing m a) wJ sigmaI sigmaJ tau = 0} = 0 := by
  let base :=
    gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI (affinePricing m a) sigmaI sigmaJ Ri Rj
  have hbase_continuous : ContinuousOn base (Set.Ioi 0) := by
    dsimp [base]
    simpa [gn21MeasuredLeftLemma6ResponseAtCurrent, affinePricing] using
      (continuousOn_affine_gn21Lemma6Response_ctmc
        m a
        (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
        (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
        (gn21ScaledStateTime muI arrivalI sigmaI)
        (gn21ScaledStateTime muJ arrivalJ sigmaJ)
        Ri Rj switchIJ switchJI)
  have hbase_anti : StrictAntiOn base (Set.Ioi 0) := by
    dsimp [base]
    exact strictAntiOn_gn21MeasuredLeft_positiveAffineLemma6Response
      muI muJ arrivalI arrivalJ switchIJ switchJI m a Ri Rj sigmaI sigmaJ
      hRi_lt_Rj ha_nonneg hstate_weight_pos hswitchIJ_pos hsum
  rcases strictAnti_sourcePolicyForm_and_zeroSetNull_of_continuousOn
      muI base hbase_continuous hbase_anti with ⟨hbase_form, hbase_zero⟩
  exact gn21MeasuredLeft_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6
    muI muJ arrivalI arrivalJ switchIJ switchJI (affinePricing m a) wJ
    sigmaI sigmaJ Ri Rj .strictlyDecreasing hbase_form hbase_zero
    hQj_pos hTi_pos hTj_pos hden_pos hWi hWj

/--
The surge affine-minus branch transferred to the actual Appendix-D marginal
response.  Its source statement must retain the empty positive-response
alternative: the printed finite right cutoff is recovered only at an actual
optimum after a separate positive-mass argument.
-/
theorem gn21MeasuredRight_negativeAffineMarginal_sourceForm_or_empty_and_zeroSetNull
    (muI muJ : Measure TripLength) [NoAtoms muJ]
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (wI : PricingFunction)
    (sigmaI sigmaJ : TripPolicy)
    (hRi_lt_Rj : Ri < Rj)
    (ha_nonneg : 0 <= a)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hswitchJI_pos : 0 < switchJI)
    (hsum : 0 < switchJI + switchIJ)
    (hQi_pos :
      0 < gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI wI sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ (affinePricing m (-a)) sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    (lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wI (affinePricing m (-a)) sigmaI sigmaJ)) \/
      lemma5PositiveResponsePolicy
        (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
          switchIJ switchJI wI (affinePricing m (-a)) sigmaI sigmaJ) = ∅) /\
      muJ
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI (affinePricing m (-a)) sigmaI sigmaJ tau = 0} = 0 := by
  let base :=
    gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI (affinePricing m (-a)) sigmaI sigmaJ Ri Rj
  have hbase_continuous : ContinuousOn base (Set.Ioi 0) := by
    dsimp [base]
    simpa [gn21MeasuredRightLemma6ResponseAtCurrent, affinePricing, add_comm,
      add_left_comm, add_assoc] using
      (continuousOn_affine_gn21Lemma6Response_ctmc
        m (-a)
        (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
        (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
        (gn21ScaledStateTime muJ arrivalJ sigmaJ)
        (gn21ScaledStateTime muI arrivalI sigmaI)
        Rj Ri switchJI switchIJ)
  have hbase_mono : StrictMonoOn base (Set.Ioi 0) := by
    dsimp [base]
    exact strictMonoOn_gn21MeasuredRight_negativeAffineLemma6Response
      muI muJ arrivalI arrivalJ switchIJ switchJI m a Ri Rj sigmaI sigmaJ
      hRi_lt_Rj ha_nonneg hstate_weight_pos hswitchJI_pos hsum
  rcases strictMono_sourcePolicyForm_or_positiveResponse_empty_and_zeroSetNull_of_continuousOn
      muJ base hbase_continuous hbase_mono with
    ⟨hbase_form_or_empty, hbase_zero⟩
  exact
    lemma5SourcePolicyForm_or_positiveResponse_empty_and_zeroSetNull_of_positive_scaling
      muJ base
      (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
        switchIJ switchJI wI (affinePricing m (-a)) sigmaI sigmaJ)
      (gn21MeasuredRightLemma6ScaleAtCurrent muI muJ arrivalI arrivalJ
        switchIJ switchJI sigmaI sigmaJ)
      hbase_form_or_empty hbase_zero
      (by
        intro tau htau
        exact gn21MeasuredRightLemma6ScaleAtCurrent_pos
          muI muJ arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ
          hQi_pos hTi_pos hTj_pos hden_pos htau)
      (by
        intro tau htau
        exact gn21MeasuredRightMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
          muI muJ arrivalI arrivalJ switchIJ switchJI wI (affinePricing m (-a))
          sigmaI sigmaJ Ri Rj tau (ne_of_gt hden_pos) (ne_of_gt htau)
          (ne_of_gt hTi_pos) (ne_of_gt hTj_pos) hWi hWj)

/--
At a genuine source-open optimum, the surge affine-minus branch has the
printed finite right-cutoff form.  The two facts that rule out the otherwise
valid empty branch are derived here from the actual model: source surge
dominance gives positive current surge mass, and open optimality gives the
comparison with the empty surge policy.  Neither is an added certificate
field.
-/
theorem gn21MeasuredRight_negativeAffineMarginal_sourceFiniteForm_and_zeroSetNull_of_dynamicOpenOptimal
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 1)] [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    (m a : Real)
    (hw1_affine : w 1 = affinePricing m (-a))
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (ha_nonneg : 0 <= a)
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hq1 :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        acceptAllPolicy (mu 1))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    {rho : Fin 2 -> TripPolicy}
    (hrho : dynamicOpenOptimal
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho) :
    lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 0) (w 1) (rho 0) (rho 1))) /\
      (mu 1)
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (w 0) (w 1) (rho 0) (rho 1) tau = 0} = 0 := by
  have hrho_meas : dynamicFeasibleMeasurablePolicy rho := hrho.1.to_measurable
  have hrho0_subset : rho 0 ⊆ acceptAllPolicy := (hrho_meas 0).1
  have hrho0_meas : MeasurableSet (rho 0) := (hrho_meas 0).2
  have hrho1_subset : rho 1 ⊆ acceptAllPolicy := (hrho_meas 1).1
  have hrho1_meas : MeasurableSet (rho 1) := (hrho_meas 1).2
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hQ0_pos :
      0 < gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 0) (arrival 0) switch12 switch21
      (rho 0) (le_of_lt harrival0_pos) hswitch12_pos hsum0
      hrho0_meas hrho0_subset
  have hQ1_pos :
      0 < gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) :=
    gn21ExitWeightIntegral_pos_of_switch_pos (mu 1) (arrival 1) switch21 switch12
      (rho 1) (le_of_lt harrival1_pos) hswitch21_pos hsum1
      hrho1_meas hrho1_subset
  have hT0_pos : 0 < gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 0) (arrival 0) (rho 0)
      (le_of_lt harrival0_pos) hrho0_meas hrho0_subset
  have hT1_pos : 0 < gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateTime_pos_of_nonneg (mu 1) (arrival 1) (rho 1)
      (le_of_lt harrival1_pos) hrho1_meas hrho1_subset
  have hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (mul_pos hQ0_pos hT1_pos) (mul_pos hQ1_pos hT0_pos)
  let Ri := gn21MeasuredStateRewardRate (mu 0) (arrival 0) (w 0) (rho 0)
  let Rj := gn21MeasuredStateRewardRate (mu 1) (arrival 1) (w 1) (rho 1)
  have hWi :
      gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0) =
        Ri * gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 0) (arrival 0) Ri (w 0) (rho 0)
      harrival0_pos hrho0_meas hrho0_subset rfl
  have hWj :
      gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1) =
        Rj * gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) :=
    gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate_endpoint
      (mu 1) (arrival 1) Rj (w 1) (rho 1)
      harrival1_pos hrho1_meas hrho1_subset rfl
  have hRi_lt_Rj : Ri < Rj := by
    dsimp [Ri, Rj]
    exact gn21MeasuredStateRewardRate_lt_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge hrho
  have hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) /
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) /
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) :=
    add_pos (div_pos hQ1_pos hT1_pos) (div_pos hQ0_pos hT0_pos)
  let base :=
    gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21
      (w 1) (rho 0) (rho 1) Ri Rj
  let marginal :=
    gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1)
  have hbase_continuous : ContinuousOn base (Set.Ioi 0) := by
    dsimp [base]
    rw [hw1_affine]
    simpa [gn21MeasuredRightLemma6ResponseAtCurrent, affinePricing, add_comm,
      add_left_comm, add_assoc] using
      (continuousOn_affine_gn21Lemma6Response_ctmc
        m (-a)
        (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
        (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
        (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
        (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
        Rj Ri switch21 switch12)
  have hbase_mono : StrictMonoOn base (Set.Ioi 0) := by
    dsimp [base]
    rw [hw1_affine]
    exact strictMonoOn_gn21MeasuredRight_negativeAffineLemma6Response
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      m a Ri Rj (rho 0) (rho 1) hRi_lt_Rj ha_nonneg hstate_weight_pos
      hswitch21_pos hsum1
  have hmass : 0 < singleStateTripMass (mu 1) (rho 1) :=
    gn21PositiveSurgeMass_of_dynamicOpenOptimal_and_sourceSurgeStateDominance
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hsurge hrho
  have hmarginal_integrable : IntegrableOn marginal acceptAllPolicy (mu 1) := by
    dsimp [marginal]
    exact integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1) acceptAllPolicy hq1 hw1 htime1
  have hempty_comparison :
      lemma5MarginalSetReward (mu 1) marginal ∅ <=
        lemma5MarginalSetReward (mu 1) marginal (rho 1) := by
    dsimp [marginal]
    exact gn21MeasuredRightMarginalSetReward_empty_le_of_dynamicOpenOptimal_direct
      mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
      hswitch12_pos hswitch21_pos hq1 hw1 htime1
  have hnegative_transfer :
      forall tau : TripLength, 0 < tau -> base tau < 0 -> marginal tau < 0 := by
    intro tau htau hbase_neg
    have hscale_pos :
        0 < gn21MeasuredRightLemma6ScaleAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21 (rho 0) (rho 1) tau :=
      gn21MeasuredRightLemma6ScaleAtCurrent_pos
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (rho 0) (rho 1) hQ0_pos hT0_pos hT1_pos hden_pos htau
    have hscale_eq :
        marginal tau =
          gn21MeasuredRightLemma6ScaleAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21 (rho 0) (rho 1) tau *
            base tau := by
      dsimp [marginal, base]
      exact gn21MeasuredRightMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (rho 0) (rho 1) Ri Rj tau
        (ne_of_gt hden_pos) (ne_of_gt htau) (ne_of_gt hT0_pos)
        (ne_of_gt hT1_pos) hWi hWj
    rw [hscale_eq]
    exact mul_neg_of_pos_of_neg hscale_pos hbase_neg
  rcases strictMono_sourcePolicyForm_and_zeroSetNull_of_scaled_emptyComparison
      (mu 1) base marginal (rho 1) hrho1_meas hrho1_subset hmass
      hmarginal_integrable hempty_comparison hnegative_transfer hbase_continuous
      hbase_mono with ⟨hbase_form, hbase_zero⟩
  have hbase_form' :
      lemma5SourcePolicyForm .strictlyIncreasing
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21
            (w 1) (rho 0) (rho 1) Ri Rj)) := by
    simpa [base] using hbase_form
  have hbase_zero' :
      (mu 1)
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightLemma6ResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21
              (w 1) (rho 0) (rho 1) Ri Rj tau = 0} = 0 := by
    simpa [base] using hbase_zero
  exact gn21MeasuredRight_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6
    (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
    (w 0) (w 1) (rho 0) (rho 1) Ri Rj .strictlyIncreasing
    hbase_form' hbase_zero' hQ0_pos hT0_pos hT1_pos hden_pos hWi hWj

/--
Lemma 7's source primitives prove the normalized positive-affine two-tail
form and its null zero boundary.  The endpoint-complete classification is
derived from continuity and strict quasi-convexity, not from an endpoint
derivative or a separately assumed cutoff sign.
-/
theorem affinePositiveLemma6_sourceTwoTailForm_and_zeroSetNull
    (mu : Measure TripLength) [NoAtoms mu]
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : Real)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 <= Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    lemma5SourcePolicyForm .strictlyQuasiConvex
      (lemma5PositiveResponsePolicy
        (fun tau : TripLength =>
          gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
            (m * tau + a) Qi Qj Ti Tj Ri Rj)) /\
      mu
        {tau : TripLength |
          0 < tau /\
            gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj = 0} = 0 := by
  let response : TripLength -> Real := fun tau =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
      (m * tau + a) Qi Qj Ti Tj Ri Rj
  have hquasi : strictQuasiConvexOnPositive response := by
    exact paper_lemma7_affine_ctmc_response_quasi_convex
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_pos hgap_nonneg hlambdaIJ hsum hTi hTj
  constructor
  · exact lemma5SourcePolicyForm_positiveResponse_of_strictQuasiConvex_continuousOn
      response
      (continuousOn_affine_gn21Lemma6Response_ctmc
        m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI)
      hquasi
  · exact measure_positiveZeroSet_eq_zero_of_strictQuasiConvex
      mu response hquasi

/--
Lemma 8's source primitives alone now prove the normalized negative-affine
middle form and its null zero boundary; no cutoff or endpoint-calculus premise
is needed for this classification.
-/
theorem affineNegativeLemma6_sourceMiddleForm_and_zeroSetNull
    (mu : Measure TripLength) [NoAtoms mu]
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : Real)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 <= Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    lemma5SourcePolicyForm .strictlyQuasiConcave
      (lemma5PositiveResponsePolicy
        (fun tau : TripLength =>
          gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
            (m * tau + a) Qi Qj Ti Tj Ri Rj)) /\
      mu
        {tau : TripLength |
          0 < tau /\
            gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj = 0} = 0 := by
  let response : TripLength -> Real := fun tau =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
      (m * tau + a) Qi Qj Ti Tj Ri Rj
  have hquasi : strictQuasiConcaveOnPositive response := by
    exact paper_lemma8_affine_ctmc_response_quasi_concave
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_neg hgap_nonneg hlambdaIJ hsum hTi hTj
  constructor
  · exact lemma5SourcePolicyForm_positiveResponse_of_strictQuasiConcave_continuousOn
      response
      (continuousOn_affine_gn21Lemma6Response_ctmc
        m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI)
      hquasi
  · exact measure_positiveZeroSet_eq_zero_of_strictQuasiConcave
      mu response hquasi

/--
Lemma 8 specialized to the actual non-surge GN21 aggregate primitives.  This
is the source-exact normalized response classification needed before the
positive measured-marginal scale is applied.
-/
theorem gn21MeasuredLeft_negativeAffineLemma6_sourceMiddleForm_and_zeroSetNull
    (muI muJ : Measure TripLength) [NoAtoms muI]
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (sigmaI sigmaJ : TripPolicy)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 <= Rj - Ri)
    (hswitchIJ_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hTi : gn21ScaledStateTime muI arrivalI sigmaI ≠ 0)
    (hTj : gn21ScaledStateTime muJ arrivalJ sigmaJ ≠ 0) :
    lemma5SourcePolicyForm .strictlyQuasiConcave
      (lemma5PositiveResponsePolicy
        (gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
          switchIJ switchJI (affinePricing m a) sigmaI sigmaJ Ri Rj)) /\
      muI
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI (affinePricing m a) sigmaI sigmaJ Ri Rj tau = 0} = 0 := by
  simpa [gn21MeasuredLeftLemma6ResponseAtCurrent, affinePricing] using
    affineNegativeLemma6_sourceMiddleForm_and_zeroSetNull
      muI m a
      (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
      (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
      (gn21ScaledStateTime muI arrivalI sigmaI)
      (gn21ScaledStateTime muJ arrivalJ sigmaJ)
      Ri Rj switchIJ switchJI hstate_weight_pos ha_neg hgap_nonneg
      hswitchIJ_pos hsum hTi hTj

/--
Lemma 7 specialized to the actual surge-side GN21 aggregate primitives.  It
classifies the normalized positive-affine response as an extended two-tail
policy and proves its zero boundary null.
-/
theorem gn21MeasuredRight_positiveAffineLemma6_sourceTwoTailForm_and_zeroSetNull
    (muI muJ : Measure TripLength) [NoAtoms muJ]
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (sigmaI sigmaJ : TripPolicy)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 <= Rj - Ri)
    (hswitchJI_pos : 0 < switchJI)
    (hsum : 0 < switchJI + switchIJ)
    (hTj : gn21ScaledStateTime muJ arrivalJ sigmaJ ≠ 0)
    (hTi : gn21ScaledStateTime muI arrivalI sigmaI ≠ 0) :
    lemma5SourcePolicyForm .strictlyQuasiConvex
      (lemma5PositiveResponsePolicy
        (gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
          switchIJ switchJI (affinePricing m a) sigmaI sigmaJ Ri Rj)) /\
      muJ
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI (affinePricing m a) sigmaI sigmaJ Ri Rj tau = 0} = 0 := by
  -- The source's surge response swaps the two fixed-state primitives.
  simpa [gn21MeasuredRightLemma6ResponseAtCurrent, affinePricing, add_comm,
    add_left_comm, add_assoc] using
    affinePositiveLemma6_sourceTwoTailForm_and_zeroSetNull
      muJ m a
      (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
      (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
      (gn21ScaledStateTime muJ arrivalJ sigmaJ)
      (gn21ScaledStateTime muI arrivalI sigmaI)
      Rj Ri switchJI switchIJ hstate_weight_pos ha_pos hgap_nonneg
      hswitchJI_pos hsum hTj hTi

/--
The non-surge negative-affine Lemma 8 form transferred to the actual
Appendix-D marginal response.  This is an ordinary scale calculation, not a
policy-form certificate.
-/
theorem gn21MeasuredLeft_negativeAffineMarginal_sourceMiddleForm_and_zeroSetNull
    (muI muJ : Measure TripLength) [NoAtoms muI]
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (wJ : PricingFunction)
    (sigmaI sigmaJ : TripPolicy)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 <= Rj - Ri)
    (hswitchIJ_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hQj_pos :
      0 < gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI (affinePricing m a) sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    lemma5SourcePolicyForm .strictlyQuasiConcave
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI (affinePricing m a) wJ sigmaI sigmaJ)) /\
      muI
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI (affinePricing m a) wJ sigmaI sigmaJ tau = 0} = 0 := by
  rcases gn21MeasuredLeft_negativeAffineLemma6_sourceMiddleForm_and_zeroSetNull
      muI muJ arrivalI arrivalJ switchIJ switchJI m a Ri Rj sigmaI sigmaJ
      hstate_weight_pos ha_neg hgap_nonneg hswitchIJ_pos hsum
      (ne_of_gt hTi_pos) (ne_of_gt hTj_pos) with ⟨hbase_form, hbase_zero⟩
  exact gn21MeasuredLeft_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6
    muI muJ arrivalI arrivalJ switchIJ switchJI (affinePricing m a) wJ
    sigmaI sigmaJ Ri Rj .strictlyQuasiConcave hbase_form hbase_zero
    hQj_pos hTi_pos hTj_pos hden_pos hWi hWj

/--
The surge positive-affine Lemma 7 form transferred to the actual Appendix-D
marginal response.  Its two-tail source family already includes the empty
endpoint, so no extra nonemptiness premise is needed.
-/
theorem gn21MeasuredRight_positiveAffineMarginal_sourceTwoTailForm_and_zeroSetNull
    (muI muJ : Measure TripLength) [NoAtoms muJ]
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (m a Ri Rj : Real) (wI : PricingFunction)
    (sigmaI sigmaJ : TripPolicy)
    (hstate_weight_pos :
      0 <
        gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ /
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI /
            gn21ScaledStateTime muI arrivalI sigmaI)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 <= Rj - Ri)
    (hswitchJI_pos : 0 < switchJI)
    (hsum : 0 < switchJI + switchIJ)
    (hQi_pos :
      0 < gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI wI sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ (affinePricing m a) sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    lemma5SourcePolicyForm .strictlyQuasiConvex
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wI (affinePricing m a) sigmaI sigmaJ)) /\
      muJ
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI (affinePricing m a) sigmaI sigmaJ tau = 0} = 0 := by
  rcases gn21MeasuredRight_positiveAffineLemma6_sourceTwoTailForm_and_zeroSetNull
      muI muJ arrivalI arrivalJ switchIJ switchJI m a Ri Rj sigmaI sigmaJ
      hstate_weight_pos ha_pos hgap_nonneg hswitchJI_pos hsum
      (ne_of_gt hTj_pos) (ne_of_gt hTi_pos) with ⟨hbase_form, hbase_zero⟩
  exact gn21MeasuredRight_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6
    muI muJ arrivalI arrivalJ switchIJ switchJI wI (affinePricing m a)
    sigmaI sigmaJ Ri Rj .strictlyQuasiConvex hbase_form hbase_zero
    hQi_pos hTi_pos hTj_pos hden_pos hWi hWj

/--
Sign conditions on the two sides of an extended middle interval identify the
positive-response policy exactly.  These are the cutoff obligations that the
affine analysis must establish; they are not a conclusion-bearing record.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_extendedMiddle_signs
    (response : TripLength -> Real)
    (lower upper : ENNReal)
    (hinside :
      forall tau : TripLength,
        tau ∈ gn21ExtendedMiddlePolicy lower upper -> 0 < response tau)
  (houtside :
      forall tau : TripLength,
        0 < tau ->
        tau ∉ gn21ExtendedMiddlePolicy lower upper ->
          response tau <= 0) :
    lemma5SourcePolicyForm .strictlyQuasiConcave
      (lemma5PositiveResponsePolicy response) := by
  refine ⟨lower, upper, ?_⟩
  ext tau
  constructor
  · intro htau
    by_contra htau_not_mem
    exact (not_lt_of_ge (houtside tau htau.1 htau_not_mem)) htau.2
  · intro htau
    have htau_pos : 0 < tau :=
      gn21ExtendedMiddlePolicy_subset_acceptAll lower upper htau
    exact ⟨htau_pos, hinside tau htau⟩

/--
Sign conditions on the two sides of an extended two-tail policy identify the
positive-response policy exactly.  These are likewise explicit cutoff
obligations, not an endpoint-variation assumption.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_extendedTwoTail_signs
    (response : TripLength -> Real)
    (lower upper : ENNReal)
    (hinside :
      forall tau : TripLength,
        tau ∈ gn21ExtendedTwoTailPolicy lower upper -> 0 < response tau)
  (houtside :
      forall tau : TripLength,
        0 < tau ->
        tau ∉ gn21ExtendedTwoTailPolicy lower upper ->
          response tau <= 0) :
    lemma5SourcePolicyForm .strictlyQuasiConvex
      (lemma5PositiveResponsePolicy response) := by
  refine ⟨lower, upper, ?_⟩
  ext tau
  constructor
  · intro htau
    by_contra htau_not_mem
    exact (not_lt_of_ge (houtside tau htau.1 htau_not_mem)) htau.2
  · intro htau
    have htau_pos : 0 < tau :=
      gn21ExtendedTwoTailPolicy_subset_acceptAll lower upper htau
    exact ⟨htau_pos, hinside tau htau⟩

/--
The negative-affine normalized Lemma 6 response has a source-exact extended
middle form once its explicit cutoff signs are established.  Its zero boundary
is already discharged from Lemma 8's strict quasi-concavity and nonatomicity.
-/
theorem affineNegativeLemma6_sourceMiddleForm_and_zeroSetNull_of_signs
    (mu : Measure TripLength) [NoAtoms mu]
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : Real)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 <= Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0)
    (lower upper : ENNReal)
    (hinside :
      forall tau : TripLength,
        tau ∈ gn21ExtendedMiddlePolicy lower upper ->
          0 <
            gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj)
    (houtside :
      forall tau : TripLength,
        0 < tau ->
        tau ∉ gn21ExtendedMiddlePolicy lower upper ->
          gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj <= 0) :
    lemma5SourcePolicyForm .strictlyQuasiConcave
      (lemma5PositiveResponsePolicy
        (fun tau : TripLength =>
          gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
            (m * tau + a) Qi Qj Ti Tj Ri Rj)) /\
      mu
        {tau : TripLength |
          0 < tau /\
            gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj = 0} = 0 := by
  let response : TripLength -> Real := fun tau =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
      (m * tau + a) Qi Qj Ti Tj Ri Rj
  have hquasi : strictQuasiConcaveOnPositive response := by
    exact paper_lemma8_affine_ctmc_response_quasi_concave
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_neg hgap_nonneg hlambdaIJ hsum hTi hTj
  constructor
  · exact lemma5SourcePolicyForm_positiveResponse_of_extendedMiddle_signs
      response lower upper hinside houtside
  · exact measure_positiveZeroSet_eq_zero_of_strictQuasiConcave
      mu response hquasi

/--
The positive-affine normalized Lemma 6 response has a source-exact extended
two-tail form once its explicit cutoff signs are established.  Lemma 7's
strict quasi-convexity proves the zero boundary null automatically.
-/
theorem affinePositiveLemma6_sourceTwoTailForm_and_zeroSetNull_of_signs
    (mu : Measure TripLength) [NoAtoms mu]
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : Real)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 <= Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0)
    (lower upper : ENNReal)
    (hinside :
      forall tau : TripLength,
        tau ∈ gn21ExtendedTwoTailPolicy lower upper ->
          0 <
            gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj)
    (houtside :
      forall tau : TripLength,
        0 < tau ->
        tau ∉ gn21ExtendedTwoTailPolicy lower upper ->
          gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj <= 0) :
    lemma5SourcePolicyForm .strictlyQuasiConvex
      (lemma5PositiveResponsePolicy
        (fun tau : TripLength =>
          gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
            (m * tau + a) Qi Qj Ti Tj Ri Rj)) /\
      mu
        {tau : TripLength |
          0 < tau /\
            gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
              (m * tau + a) Qi Qj Ti Tj Ri Rj = 0} = 0 := by
  let response : TripLength -> Real := fun tau =>
    gn21Lemma6Response (gn21SwitchProb lambdaIJ lambdaJI tau) tau
      (m * tau + a) Qi Qj Ti Tj Ri Rj
  have hquasi : strictQuasiConvexOnPositive response := by
    exact paper_lemma7_affine_ctmc_response_quasi_convex
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_pos hgap_nonneg hlambdaIJ hsum hTi hTj
  constructor
  · exact lemma5SourcePolicyForm_positiveResponse_of_extendedTwoTail_signs
      response lower upper hinside houtside
  · exact measure_positiveZeroSet_eq_zero_of_strictQuasiConvex
      mu response hquasi

/--
For the actual Appendix-D aggregate reward, a non-surge global optimizer has
the source-exact form of its positive measured marginal response.  The two
response-set obligations remain explicit so affine analysis cannot be replaced
by an endpoint-calculus certificate.
-/
theorem gn21Aggregate_left_sourcePolicyFormAlmostEverywhere_of_dynamic_optimal
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicMeasurableOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hq_integrable :
      forall sigma : TripPolicy,
        sigma ⊆ acceptAllPolicy ->
        MeasurableSet sigma ->
          IntegrableOn
            (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
            sigma (mu 0))
    (hw_integrable :
      forall sigma : TripPolicy,
        sigma ⊆ acceptAllPolicy ->
        MeasurableSet sigma ->
          IntegrableOn (w 0) sigma (mu 0))
    (htime_integrable :
      forall sigma : TripPolicy,
        sigma ⊆ acceptAllPolicy ->
        MeasurableSet sigma ->
          IntegrableOn (fun tau : TripLength => tau) sigma (mu 0))
    (shape : Lemma5DerivativeShape)
    (hresponse_measurable :
      Measurable
        (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (rho 0) (rho 1)))
    (hresponse_integrable_acceptAll :
      IntegrableOn
        (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (rho 0) (rho 1))
        acceptAllPolicy (mu 0))
    (hpositive_response_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
            (rho 0) (rho 1))))
    (hpositive_zero_set_null :
      (mu 0)
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
              (rho 0) (rho 1) tau = 0} = 0) :
    lemma5SourcePolicyFormAlmostEverywhere (mu 0) shape (rho 0) := by
  apply lemma5SourcePolicyFormAlmostEverywhere_of_fixedMarginal_optimal
    (mu 0)
    (gn21MeasuredLeftMarginalResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (rho 0) (rho 1))
    shape (rho 0) hresponse_measurable hresponse_integrable_acceptAll
    (hrho.1 0).2 (hrho.1 0).1 hpositive_response_form
    hpositive_zero_set_null
  intro sigma hsigma_subset hsigma_measurable
  exact lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_zero
    mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hq_integrable hw_integrable htime_integrable
    sigma hsigma_subset hsigma_measurable

/--
For the actual Appendix-D aggregate reward, a surge global optimizer has the
source-exact form of its positive measured marginal response.  This is the
state-symmetric fixed-marginal route and likewise contains no endpoint path.
-/
theorem gn21Aggregate_right_sourcePolicyFormAlmostEverywhere_of_dynamic_optimal
    (mu : Fin 2 -> Measure TripLength)
    (arrival : Fin 2 -> Real)
    (switch12 switch21 : Real)
    (w : Fin 2 -> PricingFunction)
    {rho : Fin 2 -> TripPolicy}
    (hrho :
      dynamicMeasurableOptimal
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) rho)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hq_integrable :
      forall sigma : TripPolicy,
        sigma ⊆ acceptAllPolicy ->
        MeasurableSet sigma ->
          IntegrableOn
            (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
            sigma (mu 1))
    (hw_integrable :
      forall sigma : TripPolicy,
        sigma ⊆ acceptAllPolicy ->
        MeasurableSet sigma ->
          IntegrableOn (w 1) sigma (mu 1))
    (htime_integrable :
      forall sigma : TripPolicy,
        sigma ⊆ acceptAllPolicy ->
        MeasurableSet sigma ->
          IntegrableOn (fun tau : TripLength => tau) sigma (mu 1))
    (shape : Lemma5DerivativeShape)
    (hresponse_measurable :
      Measurable
        (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (rho 0) (rho 1)))
    (hresponse_integrable_acceptAll :
      IntegrableOn
        (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (rho 0) (rho 1))
        acceptAllPolicy (mu 1))
    (hpositive_response_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
            (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
            (rho 0) (rho 1))))
    (hpositive_zero_set_null :
      (mu 1)
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
              (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
              (rho 0) (rho 1) tau = 0} = 0) :
    lemma5SourcePolicyFormAlmostEverywhere (mu 1) shape (rho 1) := by
  apply lemma5SourcePolicyFormAlmostEverywhere_of_fixedMarginal_optimal
    (mu 1)
    (gn21MeasuredRightMarginalResponseAtCurrent (mu 0) (mu 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (rho 0) (rho 1))
    shape (rho 1) hresponse_measurable hresponse_integrable_acceptAll
    (hrho.1 1).2 (hrho.1 1).1 hpositive_response_form
    hpositive_zero_set_null
  intro sigma hsigma_subset hsigma_measurable
  exact lemma5MarginalSetReward_optimal_of_gn21AggregateDynamicRewardFunctional_one
    mu arrival switch12 switch21 w hrho harrival0_pos harrival1_pos
    hswitch12_pos hswitch21_pos hq_integrable hw_integrable htime_integrable
    sigma hsigma_subset hsigma_measurable

/--
Transfer a source-exact positive-set classification of the normalized left
Lemma 6 response to the actual left measured marginal response.
-/
theorem gn21MeasuredLeft_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6Response
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    (Ri Rj : Real) (shape : Lemma5DerivativeShape)
    (hbase_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wI sigmaI sigmaJ Ri Rj)))
    (hbase_zero_set_null :
      muI
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI sigmaI sigmaJ Ri Rj tau = 0} = 0)
    (hQj_pos :
      0 < gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI wI sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    lemma5SourcePolicyForm shape
      (lemma5PositiveResponsePolicy
        (gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
          switchIJ switchJI wI wJ sigmaI sigmaJ)) /\
      muI
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI wJ sigmaI sigmaJ tau = 0} = 0 := by
  apply lemma5SourcePolicyForm_and_zeroSetNull_of_positive_scaling
    muI
    (gn21MeasuredLeftLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wI sigmaI sigmaJ Ri Rj)
    (gn21MeasuredLeftMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wI wJ sigmaI sigmaJ)
    (gn21MeasuredLeftLemma6ScaleAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ)
    shape hbase_form hbase_zero_set_null
  · intro tau htau
    exact gn21MeasuredLeftLemma6ScaleAtCurrent_pos muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ hQj_pos hTi_pos hTj_pos hden_pos htau
  · intro tau htau
    exact gn21MeasuredLeftMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
      muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ Ri Rj
      tau (ne_of_gt hden_pos) (ne_of_gt htau) (ne_of_gt hTi_pos)
      (ne_of_gt hTj_pos) hWi hWj

/--
Transfer a source-exact positive-set classification of the normalized right
Lemma 6 response to the actual right measured marginal response.
-/
theorem gn21MeasuredRight_sourcePolicyForm_and_zeroSetNull_of_scaled_lemma6Response
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    (Ri Rj : Real) (shape : Lemma5DerivativeShape)
    (hbase_form :
      lemma5SourcePolicyForm shape
        (lemma5PositiveResponsePolicy
          (gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
            switchIJ switchJI wJ sigmaI sigmaJ Ri Rj)))
    (hbase_zero_set_null :
      muJ
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wJ sigmaI sigmaJ Ri Rj tau = 0} = 0)
    (hQi_pos :
      0 < gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
    (hTi_pos : 0 < gn21ScaledStateTime muI arrivalI sigmaI)
    (hTj_pos : 0 < gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ScaledStateEarning muI arrivalI wI sigmaI =
        Ri * gn21ScaledStateTime muI arrivalI sigmaI)
    (hWj :
      gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ =
        Rj * gn21ScaledStateTime muJ arrivalJ sigmaJ) :
    lemma5SourcePolicyForm shape
      (lemma5PositiveResponsePolicy
        (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
          switchIJ switchJI wI wJ sigmaI sigmaJ)) /\
      muJ
        {tau : TripLength |
          0 < tau /\
            gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
              switchIJ switchJI wI wJ sigmaI sigmaJ tau = 0} = 0 := by
  apply lemma5SourcePolicyForm_and_zeroSetNull_of_positive_scaling
    muJ
    (gn21MeasuredRightLemma6ResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wJ sigmaI sigmaJ Ri Rj)
    (gn21MeasuredRightMarginalResponseAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI wI wJ sigmaI sigmaJ)
    (gn21MeasuredRightLemma6ScaleAtCurrent muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ)
    shape hbase_form hbase_zero_set_null
  · intro tau htau
    exact gn21MeasuredRightLemma6ScaleAtCurrent_pos muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ hQi_pos hTi_pos hTj_pos hden_pos htau
  · intro tau htau
    exact gn21MeasuredRightMarginalResponse_eq_scale_mul_lemma6ResponseAtCurrent
      muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ Ri Rj
      tau (ne_of_gt hden_pos) (ne_of_gt htau) (ne_of_gt hTi_pos)
      (ne_of_gt hTj_pos) hWi hWj

/--
An explicit sign description of a positive-response set gives the source's
extended middle-interval form.  The endpoints may be zero or infinity.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_extendedMiddle
    (response : TripLength -> Real)
    (lower upper : ENNReal)
    (hpositive_iff :
      forall tau : TripLength,
        0 < tau ->
          (0 < response tau ↔ tau ∈ gn21ExtendedMiddlePolicy lower upper)) :
    lemma5SourcePolicyForm .strictlyQuasiConcave
      (lemma5PositiveResponsePolicy response) := by
  refine ⟨lower, upper, ?_⟩
  ext tau
  constructor
  · intro htau
    exact hpositive_iff tau htau.1 |>.mp htau.2
  · intro htau
    have htau_pos : 0 < tau :=
      gn21ExtendedMiddlePolicy_subset_acceptAll lower upper htau
    exact ⟨htau_pos, (hpositive_iff tau htau_pos).mpr htau⟩

/--
An explicit sign description of a positive-response set gives the source's
extended two-tail form.  The endpoints may be zero or infinity.
-/
theorem lemma5SourcePolicyForm_positiveResponse_of_extendedTwoTail
    (response : TripLength -> Real)
    (lower upper : ENNReal)
    (hpositive_iff :
      forall tau : TripLength,
        0 < tau ->
          (0 < response tau ↔ tau ∈ gn21ExtendedTwoTailPolicy lower upper)) :
    lemma5SourcePolicyForm .strictlyQuasiConvex
      (lemma5PositiveResponsePolicy response) := by
  refine ⟨lower, upper, ?_⟩
  ext tau
  constructor
  · intro htau
    exact hpositive_iff tau htau.1 |>.mp htau.2
  · intro htau
    have htau_pos : 0 < tau :=
      gn21ExtendedTwoTailPolicy_subset_acceptAll lower upper htau
    exact ⟨htau_pos, (hpositive_iff tau htau_pos).mpr htau⟩

end GN21DriverSurgePricing
