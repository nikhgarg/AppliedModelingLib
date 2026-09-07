import GN21DriverSurgePricing.Lemma5Variational

/-!
# Direct affine canonical-family attainment for GN21 Theorem 4

This module supplies the analytic compactness input for the repaired Theorem 4
route.  It works directly with the source's endpoint-complete middle and
two-tail policies.  In particular, it does not invoke the legacy arbitrary
endpoint-union derivative interface.
-/

open AppliedModelingLib
open MeasureTheory
open scoped ENNReal Topology symmDiff

namespace GN21DriverSurgePricing

/-- Extended left cutoffs are nested in their endpoint. -/
theorem gn21LeftExtendedCutoffPolicy_subset_of_le
    {lower upper : ℝ≥0∞} (h : lower ≤ upper) :
    gn21LeftExtendedCutoffPolicy lower ⊆
      gn21LeftExtendedCutoffPolicy upper := by
  cases lower using ENNReal.recTopCoe with
  | top =>
      have hupper : upper = ∞ := top_unique h
      simp [hupper]
  | coe lower =>
      cases upper using ENNReal.recTopCoe with
      | top =>
          change rejectLongTripsPolicy (lower : ℝ) ⊆ acceptAllPolicy
          exact rejectLongTripsPolicy_subset_acceptAll (lower : ℝ)
      | coe upper =>
          have hreal : (lower : ℝ) ≤ (upper : ℝ) := by
            exact_mod_cast ENNReal.coe_le_coe.mp h
          intro tau htau
          have htau' : 0 < tau ∧ tau < (lower : ℝ) := by
            simpa [gn21LeftExtendedCutoffPolicy, rejectLongTripsPolicy] using htau
          simpa [gn21LeftExtendedCutoffPolicy, rejectLongTripsPolicy] using
            ⟨htau'.1, htau'.2.trans_le hreal⟩

/-- On ordered endpoints, the source middle interval agrees a.e. with the
difference of the corresponding left cutoffs.  The only possible discrepancy
is the lower endpoint, which is null for a nonatomic source measure. -/
theorem policyAlmostEverywhereEq_extendedMiddle_leftDiff
    (mu : Measure TripLength) [NoAtoms mu]
    {lower upper : ℝ≥0∞} (horder : lower ≤ upper) :
    policyAlmostEverywhereEq mu
      (gn21ExtendedMiddlePolicy lower upper)
      (gn21LeftExtendedCutoffPolicy upper \
        gn21LeftExtendedCutoffPolicy lower) := by
  rw [policyAlmostEverywhereEq]
  cases lower using ENNReal.recTopCoe with
  | top =>
      have hupper : upper = ∞ := top_unique horder
      simp [hupper, gn21ExtendedMiddlePolicy]
  | coe lower =>
      cases upper using ENNReal.recTopCoe with
      | top =>
          rw [gn21ExtendedMiddlePolicy_coe_top_eq_Ioi,
            gn21LeftExtendedCutoffPolicy_top,
            gn21LeftExtendedCutoffPolicy_coe]
          apply measure_mono_null ?_ (measure_singleton (lower : ℝ))
          intro tau htau
          rw [Set.mem_symmDiff] at htau
          simp only [Set.mem_Ioi, Set.mem_diff, rejectLongTripsPolicy,
            acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll,
            Set.mem_inter_iff] at htau
          rcases htau with hleft | hright
          · rcases hleft with ⟨hlower, hnotdiff⟩
            have hpos : 0 < tau := lt_of_le_of_lt lower.property hlower
            exact False.elim (hnotdiff ⟨hpos, fun hcut =>
              (not_lt_of_ge (le_of_lt hlower)) hcut.2⟩)
          · rcases hright with ⟨⟨hpos, hnotcut⟩, hnotlower⟩
            have hlower_le : (lower : ℝ) ≤ tau := by
              by_contra hlt
              exact hnotcut ⟨hpos, lt_of_not_ge hlt⟩
            exact Set.mem_singleton_iff.mpr
              (le_antisymm (le_of_not_gt hnotlower) hlower_le)
      | coe upper =>
          rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo,
            gn21LeftExtendedCutoffPolicy_coe,
            gn21LeftExtendedCutoffPolicy_coe]
          apply measure_mono_null ?_ (measure_singleton (lower : ℝ))
          intro tau htau
          rw [Set.mem_symmDiff] at htau
          simp only [Set.mem_Ioo, Set.mem_diff, rejectLongTripsPolicy,
            Set.mem_inter_iff] at htau
          rcases htau with hleft | hright
          · rcases hleft with ⟨⟨hlower, hupper⟩, hnotdiff⟩
            have hpos : 0 < tau := lt_of_le_of_lt lower.property hlower
            exact False.elim (hnotdiff ⟨⟨hpos, hupper⟩,
              fun hcut => (not_lt_of_ge (le_of_lt hlower)) hcut.2⟩)
          · rcases hright with ⟨⟨⟨hpos, hupper⟩, hnotcut⟩, hnotmiddle⟩
            have hlower_le : (lower : ℝ) ≤ tau := by
              by_contra hlt
              exact hnotcut ⟨hpos, lt_of_not_ge hlt⟩
            have hnotlower : ¬ (lower : ℝ) < tau := by
              intro hlower
              exact hnotmiddle ⟨hlower, hupper⟩
            exact Set.mem_singleton_iff.mpr
              (le_antisymm (le_of_not_gt hnotlower) hlower_le)

/-- The middle-interval integral is the difference of two nested left-cutoff
integrals, up to the nonatomic lower endpoint. -/
theorem setIntegral_extendedMiddle_eq_leftCutoff_sub
    (mu : Measure TripLength) [NoAtoms mu]
    (f : TripLength -> ℝ)
    (hfin : IntegrableOn f acceptAllPolicy mu)
    {lower upper : ℝ≥0∞} (horder : lower ≤ upper) :
    (∫ tau in gn21ExtendedMiddlePolicy lower upper, f tau ∂mu) =
      (∫ tau in gn21LeftExtendedCutoffPolicy upper, f tau ∂mu) -
        ∫ tau in gn21LeftExtendedCutoffPolicy lower, f tau ∂mu := by
  have hsubset : gn21LeftExtendedCutoffPolicy lower ⊆
      gn21LeftExtendedCutoffPolicy upper :=
    gn21LeftExtendedCutoffPolicy_subset_of_le horder
  have hupper_integrable :
      IntegrableOn f (gn21LeftExtendedCutoffPolicy upper) mu :=
    hfin.mono_set (gn21LeftExtendedCutoffPolicy_subset_acceptAll upper)
  have hdiff :
      (∫ tau in gn21LeftExtendedCutoffPolicy upper \
          gn21LeftExtendedCutoffPolicy lower, f tau ∂mu) =
        (∫ tau in gn21LeftExtendedCutoffPolicy upper, f tau ∂mu) -
          ∫ tau in gn21LeftExtendedCutoffPolicy lower, f tau ∂mu :=
    setIntegral_diff (gn21LeftExtendedCutoffPolicy_open lower).measurableSet
      hupper_integrable hsubset
  calc
    (∫ tau in gn21ExtendedMiddlePolicy lower upper, f tau ∂mu) =
        ∫ tau in gn21LeftExtendedCutoffPolicy upper \
          gn21LeftExtendedCutoffPolicy lower, f tau ∂mu :=
      setIntegral_congr_set
        (ae_eq_set_of_policyAlmostEverywhereEq mu
          (policyAlmostEverywhereEq_extendedMiddle_leftDiff mu horder))
    _ = _ := hdiff

/-- Ordered source middle intervals have continuous integrals. -/
def gn21OrderedEndpointPairs : Set (ℝ≥0∞ × ℝ≥0∞) :=
  {p | p.1 ≤ p.2}

theorem continuousOn_gn21ExtendedMiddlePolicy_setIntegral
    (mu : Measure TripLength) [NoAtoms mu] [IsFiniteMeasure mu]
    (f : TripLength -> ℝ)
    (hfin : IntegrableOn f acceptAllPolicy mu) :
    ContinuousOn
      (fun p : ℝ≥0∞ × ℝ≥0∞ =>
        ∫ tau in gn21ExtendedMiddlePolicy p.1 p.2, f tau ∂mu)
      gn21OrderedEndpointPairs := by
  let I : ℝ≥0∞ -> ℝ := fun endpoint =>
    ∫ tau in gn21LeftExtendedCutoffPolicy endpoint, f tau ∂mu
  have hI : Continuous I := by
    dsimp [I]
    exact continuous_gn21LeftExtendedCutoff_setIntegral mu f hfin
  have hcontinuous : Continuous (fun p : ℝ≥0∞ × ℝ≥0∞ => I p.2 - I p.1) :=
    (hI.comp continuous_snd).sub (hI.comp continuous_fst)
  apply hcontinuous.continuousOn.congr
  intro p hp
  exact setIntegral_extendedMiddle_eq_leftCutoff_sub mu f hfin hp

/-- The two tails are disjoint when their endpoints are ordered. -/
theorem disjoint_gn21LeftRightExtendedCutoffs_of_le
    {lower upper : ℝ≥0∞} (horder : lower ≤ upper) :
    Disjoint (gn21LeftExtendedCutoffPolicy lower)
      (gn21RightExtendedCutoffPolicy upper) := by
  refine Set.disjoint_left.2 ?_
  intro tau hleft hright
  cases lower using ENNReal.recTopCoe with
  | top =>
      have hupper : upper = ∞ := top_unique horder
      rw [hupper] at hright
      simp at hright
  | coe lower =>
      cases upper using ENNReal.recTopCoe with
      | top => simp at hright
      | coe upper =>
          have hreal : (lower : ℝ) ≤ (upper : ℝ) := by
            exact_mod_cast ENNReal.coe_le_coe.mp horder
          change tau ∈ rejectLongTripsPolicy (lower : ℝ) at hleft
          change tau ∈ rejectShortTripsPolicy (upper : ℝ) at hright
          have hleft' : 0 < tau ∧ tau < (lower : ℝ) := by
            simpa [rejectLongTripsPolicy] using hleft
          have hright' : (upper : ℝ) < tau := by
            simpa [rejectShortTripsPolicy] using hright
          exact (not_lt_of_ge hreal) (hright'.trans hleft'.2)

/-- Ordered finite middle intervals are disjoint when the first one ends no
later than the second one starts. -/
theorem disjoint_gn21ExtendedMiddlePolicy_of_upper_le_lower
    {lowerFirst upperFirst lowerSecond upperSecond : ℝ≥0∞}
    (horder : upperFirst ≤ lowerSecond) :
    Disjoint (gn21ExtendedMiddlePolicy lowerFirst upperFirst)
      (gn21ExtendedMiddlePolicy lowerSecond upperSecond) := by
  refine Set.disjoint_left.2 ?_
  intro tau hfirst hsecond
  exact (Set.disjoint_left.1
    (disjoint_gn21LeftRightExtendedCutoffs_of_le horder)) hfirst.2 hsecond.1

/-- The finitely many interval components encoded by an ordered endpoint
vector are pairwise disjoint. -/
theorem gn21EndpointVectorPolicy_pairwiseDisjoint_of_ordered
    {n : Nat} {endpoints : GN21EndpointVector n}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors n) :
    Pairwise (Function.onFun Disjoint fun i : Fin n =>
      gn21ExtendedMiddlePolicy
        (endpoints (gn21LowerEndpointIndex i))
        (endpoints (gn21UpperEndpointIndex i))) := by
  intro first second hne
  rcases lt_or_gt_of_ne hne with hfirst_second | hsecond_first
  · apply disjoint_gn21ExtendedMiddlePolicy_of_upper_le_lower
    apply hordered
    apply Fin.mk_le_mk.2
    change 2 * first.1 + 1 ≤ 2 * second.1
    omega
  · exact (disjoint_gn21ExtendedMiddlePolicy_of_upper_le_lower (by
      apply hordered
      apply Fin.mk_le_mk.2
      change 2 * second.1 + 1 ≤ 2 * first.1
      omega)).symm

/-- On an ordered endpoint vector, the set integral is the finite sum of the
integrals of its interval components. -/
theorem setIntegral_gn21EndpointVectorPolicy_eq_sum
    (mu : Measure TripLength) (f : TripLength -> ℝ)
    (hfin : IntegrableOn f acceptAllPolicy mu)
    {n : Nat} {endpoints : GN21EndpointVector n}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors n) :
    (∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu) =
      ∑ i : Fin n,
        ∫ tau in gn21ExtendedMiddlePolicy
          (endpoints (gn21LowerEndpointIndex i))
          (endpoints (gn21UpperEndpointIndex i)), f tau ∂mu := by
  unfold gn21EndpointVectorPolicy
  exact integral_iUnion_fintype
    (fun i => gn21ExtendedMiddlePolicy_measurable
      (endpoints (gn21LowerEndpointIndex i))
      (endpoints (gn21UpperEndpointIndex i)))
    (gn21EndpointVectorPolicy_pairwiseDisjoint_of_ordered hordered)
    (fun i => hfin.mono_set (gn21ExtendedMiddlePolicy_subset_acceptAll _ _))

/-- Integrals over every ordered finite endpoint family are continuous.  This
is the finite-dimensional form of the source's continuity-in-policy condition
used by Lemma 5, including its arbitrary finite Step-1 approximants. -/
theorem continuousOn_setIntegral_gn21EndpointVectorPolicy
    (mu : Measure TripLength) [NoAtoms mu] [IsFiniteMeasure mu]
    (f : TripLength -> ℝ)
    (hfin : IntegrableOn f acceptAllPolicy mu)
    (n : Nat) :
    ContinuousOn
      (fun endpoints : GN21EndpointVector n =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu)
      (gn21OrderedEndpointVectors n) := by
  have hcomponent : ∀ i : Fin n,
      ContinuousOn
        (fun endpoints : GN21EndpointVector n =>
          ∫ tau in gn21ExtendedMiddlePolicy
            (endpoints (gn21LowerEndpointIndex i))
            (endpoints (gn21UpperEndpointIndex i)), f tau ∂mu)
        (gn21OrderedEndpointVectors n) := by
    intro i
    let endpointPair : GN21EndpointVector n -> ℝ≥0∞ × ℝ≥0∞ := fun endpoints =>
      (endpoints (gn21LowerEndpointIndex i), endpoints (gn21UpperEndpointIndex i))
    have hendpointPair : Continuous endpointPair :=
      (continuous_apply (gn21LowerEndpointIndex i)).prodMk
        (continuous_apply (gn21UpperEndpointIndex i))
    have hmaps : Set.MapsTo endpointPair
        (gn21OrderedEndpointVectors n) gn21OrderedEndpointPairs := by
      intro endpoints hordered
      change endpoints (gn21LowerEndpointIndex i) ≤
        endpoints (gn21UpperEndpointIndex i)
      apply hordered
      apply Fin.mk_le_mk.2
      change 2 * i.1 ≤ 2 * i.1 + 1
      omega
    have hcomposed :=
      (continuousOn_gn21ExtendedMiddlePolicy_setIntegral mu f hfin).comp
        hendpointPair.continuousOn hmaps
    simpa [endpointPair, Function.comp_def] using hcomposed
  have hsum : ContinuousOn
      (fun endpoints : GN21EndpointVector n =>
        ∑ i : Fin n,
          ∫ tau in gn21ExtendedMiddlePolicy
            (endpoints (gn21LowerEndpointIndex i))
            (endpoints (gn21UpperEndpointIndex i)), f tau ∂mu)
      (gn21OrderedEndpointVectors n) := by
    simpa using continuousOn_finset_sum Finset.univ (fun i _ => hcomponent i)
  apply hsum.congr
  intro endpoints hordered
  exact setIntegral_gn21EndpointVectorPolicy_eq_sum mu f hfin hordered

/-- Ordered source two-tail integrals split into their two disjoint cutoff
integrals. -/
theorem setIntegral_extendedTwoTail_eq_leftCutoff_add_rightCutoff
    (mu : Measure TripLength)
    (f : TripLength -> ℝ)
    (hfin : IntegrableOn f acceptAllPolicy mu)
    {lower upper : ℝ≥0∞} (horder : lower ≤ upper) :
    (∫ tau in gn21ExtendedTwoTailPolicy lower upper, f tau ∂mu) =
      (∫ tau in gn21LeftExtendedCutoffPolicy lower, f tau ∂mu) +
        ∫ tau in gn21RightExtendedCutoffPolicy upper, f tau ∂mu := by
  rw [gn21ExtendedTwoTailPolicy]
  exact setIntegral_union
    (disjoint_gn21LeftRightExtendedCutoffs_of_le horder)
    (gn21RightExtendedCutoffPolicy_open upper).measurableSet
    (hfin.mono_set (gn21LeftExtendedCutoffPolicy_subset_acceptAll lower))
    (hfin.mono_set (gn21RightExtendedCutoffPolicy_subset_acceptAll upper))

/-- Ordered source two-tail policies have continuous integrals. -/
theorem continuousOn_gn21ExtendedTwoTailPolicy_setIntegral
    (mu : Measure TripLength) [NoAtoms mu] [IsFiniteMeasure mu]
    (f : TripLength -> ℝ)
    (hfin : IntegrableOn f acceptAllPolicy mu) :
    ContinuousOn
      (fun p : ℝ≥0∞ × ℝ≥0∞ =>
        ∫ tau in gn21ExtendedTwoTailPolicy p.1 p.2, f tau ∂mu)
      gn21OrderedEndpointPairs := by
  let Ileft : ℝ≥0∞ -> ℝ := fun endpoint =>
    ∫ tau in gn21LeftExtendedCutoffPolicy endpoint, f tau ∂mu
  let Iright : ℝ≥0∞ -> ℝ := fun endpoint =>
    ∫ tau in gn21RightExtendedCutoffPolicy endpoint, f tau ∂mu
  have hleft : Continuous Ileft := by
    dsimp [Ileft]
    exact continuous_gn21LeftExtendedCutoff_setIntegral mu f hfin
  have hright : Continuous Iright := by
    dsimp [Iright]
    exact continuous_gn21RightExtendedCutoff_setIntegral mu f hfin
  have hcontinuous : Continuous (fun p : ℝ≥0∞ × ℝ≥0∞ =>
      Ileft p.1 + Iright p.2) :=
    (hleft.comp continuous_fst).add (hright.comp continuous_snd)
  apply hcontinuous.continuousOn.congr
  intro p hp
  exact setIntegral_extendedTwoTail_eq_leftCutoff_add_rightCutoff mu f hfin hp

/-- Every compact canonical Lemma-5 endpoint family has continuous set
integrals.  The increasing family intentionally includes the compactifying
empty endpoint; finiteness is recovered only after global optimality is known. -/
theorem continuousOn_setIntegral_gn21Lemma5CanonicalEndpointPolicy
    (mu : Measure TripLength) [NoAtoms mu] [IsFiniteMeasure mu]
    (f : TripLength -> ℝ)
    (hfin : IntegrableOn f acceptAllPolicy mu)
    (shape : Lemma5DerivativeShape) :
    ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra shape) =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu)
      (gn21Lemma5CanonicalEndpointDomain shape) := by
  cases shape with
  | positive =>
      change ContinuousOn
        (fun endpoints : GN21EndpointVector 1 =>
          ∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu)
        (gn21Lemma5EndpointDomain .positive 0)
      have hconst : Continuous (fun _ : GN21EndpointVector 1 =>
          ∫ tau in acceptAllPolicy, f tau ∂mu) := continuous_const
      apply hconst.continuousOn.congr
      intro endpoints hdomain
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints 0 = 0 at hfirst
      change endpoints 1 = ∞ at hlast
      change (∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu) =
        ∫ tau in acceptAllPolicy, f tau ∂mu
      rw [gn21EndpointVectorPolicy_one, hfirst, hlast,
        gn21ExtendedMiddlePolicy_zero_top]
  | strictlyIncreasing =>
      change ContinuousOn
        (fun endpoints : GN21EndpointVector 1 =>
          ∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu)
        (gn21Lemma5EndpointDomain .strictlyIncreasing 0)
      have hright : Continuous (fun endpoints : GN21EndpointVector 1 =>
          ∫ tau in gn21RightExtendedCutoffPolicy (endpoints 0), f tau ∂mu) :=
        (continuous_gn21RightExtendedCutoff_setIntegral mu f hfin).comp
          (continuous_apply 0)
      apply hright.continuousOn.congr
      intro endpoints hdomain
      rcases hdomain with ⟨hordered, hlast⟩
      change endpoints 1 = ∞ at hlast
      change (∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu) =
        ∫ tau in gn21RightExtendedCutoffPolicy (endpoints 0), f tau ∂mu
      rw [gn21EndpointVectorPolicy_one, hlast,
        gn21ExtendedMiddlePolicy_top_right]
  | strictlyDecreasing =>
      change ContinuousOn
        (fun endpoints : GN21EndpointVector 1 =>
          ∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu)
        (gn21Lemma5EndpointDomain .strictlyDecreasing 0)
      have hleft : Continuous (fun endpoints : GN21EndpointVector 1 =>
          ∫ tau in gn21LeftExtendedCutoffPolicy (endpoints 1), f tau ∂mu) :=
        (continuous_gn21LeftExtendedCutoff_setIntegral mu f hfin).comp
          (continuous_apply 1)
      apply hleft.continuousOn.congr
      intro endpoints hdomain
      rcases hdomain with ⟨hordered, hfirst⟩
      change endpoints 0 = 0 at hfirst
      change (∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu) =
        ∫ tau in gn21LeftExtendedCutoffPolicy (endpoints 1), f tau ∂mu
      rw [gn21EndpointVectorPolicy_one, hfirst,
        gn21ExtendedMiddlePolicy_zero]
  | strictlyQuasiConvex =>
      change ContinuousOn
        (fun endpoints : GN21EndpointVector 2 =>
          ∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu)
        (gn21Lemma5EndpointDomain .strictlyQuasiConvex 1)
      let endpointPair : GN21EndpointVector 2 -> ℝ≥0∞ × ℝ≥0∞ := fun endpoints =>
        (endpoints 1, endpoints 2)
      have hendpointPair : Continuous endpointPair :=
        (continuous_apply 1).prodMk (continuous_apply 2)
      have hmaps : Set.MapsTo endpointPair
          (gn21Lemma5EndpointDomain .strictlyQuasiConvex 1)
          gn21OrderedEndpointPairs := by
        intro endpoints hdomain
        rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
        change endpoints 1 ≤ endpoints 2
        have hindex : (1 : Fin 4) ≤ (2 : Fin 4) := by decide
        exact hordered hindex
      have htail : ContinuousOn
          (fun p : ℝ≥0∞ × ℝ≥0∞ =>
            ∫ tau in gn21ExtendedTwoTailPolicy p.1 p.2, f tau ∂mu)
          gn21OrderedEndpointPairs :=
        continuousOn_gn21ExtendedTwoTailPolicy_setIntegral mu f hfin
      have hcomposed := htail.comp hendpointPair.continuousOn hmaps
      apply hcomposed.congr
      intro endpoints hdomain
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints 0 = 0 at hfirst
      change endpoints 3 = ∞ at hlast
      change (∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu) =
        ∫ tau in gn21ExtendedTwoTailPolicy (endpoints 1) (endpoints 2), f tau ∂mu
      rw [gn21EndpointVectorPolicy_two, hfirst, hlast,
        gn21ExtendedMiddlePolicy_zero,
        gn21ExtendedMiddlePolicy_top_right]
      rfl
  | strictlyQuasiConcave =>
      change ContinuousOn
        (fun endpoints : GN21EndpointVector 1 =>
          ∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu)
        (gn21Lemma5EndpointDomain .strictlyQuasiConcave 0)
      let endpointPair : GN21EndpointVector 1 -> ℝ≥0∞ × ℝ≥0∞ := fun endpoints =>
        (endpoints 0, endpoints 1)
      have hendpointPair : Continuous endpointPair :=
        (continuous_apply 0).prodMk (continuous_apply 1)
      have hmaps : Set.MapsTo endpointPair
          (gn21Lemma5EndpointDomain .strictlyQuasiConcave 0)
          gn21OrderedEndpointPairs := by
        intro endpoints hdomain
        change endpoints 0 ≤ endpoints 1
        have hindex : (0 : Fin 2) ≤ (1 : Fin 2) := by decide
        exact hdomain hindex
      have hmiddle : ContinuousOn
          (fun p : ℝ≥0∞ × ℝ≥0∞ =>
            ∫ tau in gn21ExtendedMiddlePolicy p.1 p.2, f tau ∂mu)
          gn21OrderedEndpointPairs :=
        continuousOn_gn21ExtendedMiddlePolicy_setIntegral mu f hfin
      have hcomposed := hmiddle.comp hendpointPair.continuousOn hmaps
      apply hcomposed.congr
      intro endpoints hdomain
      change (∫ tau in gn21EndpointVectorPolicy endpoints, f tau ∂mu) =
        ∫ tau in gn21ExtendedMiddlePolicy (endpoints 0) (endpoints 1), f tau ∂mu
      rw [gn21EndpointVectorPolicy_one]

/-- The actual Appendix-D aggregate objective is continuous on every compact
canonical pair once its three source integrands (time, switching weight, and
payment) are integrable.  This is the direct formal replacement for the
legacy generic endpoint-continuity field. -/
theorem continuousOn_gn21AggregateDynamicRewardFunctional_canonicalPair
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 -> PricingFunction)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1)) :
    ContinuousOn
      (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (gn21Lemma5CanonicalPairPolicy shape endpoints))
      (gn21Lemma5CanonicalPairEndpointDomain shape) := by
  let q0 : TripLength -> ℝ := fun tau => gn21SwitchProb switch12 switch21 tau
  let q1 : TripLength -> ℝ := fun tau => gn21SwitchProb switch21 switch12 tau
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 : IntegrableOn q0 acceptAllPolicy (mu 0) := by
    dsimp [q0]
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 0) switch12 switch21 acceptAllPolicy (le_of_lt hswitch12_pos)
      hsum0 (fun _ h => h) measurableSet_acceptAllPolicy htime0
  have hq1 : IntegrableOn q1 acceptAllPolicy (mu 1) := by
    dsimp [q1]
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 1) switch21 switch12 acceptAllPolicy (le_of_lt hswitch21_pos)
      hsum1 (fun _ h => h) measurableSet_acceptAllPolicy htime1
  let Iq0 : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)) -> ℝ :=
    fun endpoints => ∫ tau in gn21EndpointVectorPolicy endpoints, q0 tau ∂(mu 0)
  let Iq1 : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)) -> ℝ :=
    fun endpoints => ∫ tau in gn21EndpointVectorPolicy endpoints, q1 tau ∂(mu 1)
  let It0 : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)) -> ℝ :=
    fun endpoints => ∫ tau in gn21EndpointVectorPolicy endpoints, tau ∂(mu 0)
  let It1 : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)) -> ℝ :=
    fun endpoints => ∫ tau in gn21EndpointVectorPolicy endpoints, tau ∂(mu 1)
  let Iw0 : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)) -> ℝ :=
    fun endpoints => ∫ tau in gn21EndpointVectorPolicy endpoints, w 0 tau ∂(mu 0)
  let Iw1 : GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1)) -> ℝ :=
    fun endpoints => ∫ tau in gn21EndpointVectorPolicy endpoints, w 1 tau ∂(mu 1)
  have hIq0 : ContinuousOn Iq0 (gn21Lemma5CanonicalEndpointDomain (shape 0)) := by
    dsimp [Iq0]
    exact continuousOn_setIntegral_gn21Lemma5CanonicalEndpointPolicy
      (mu 0) q0 hq0 (shape 0)
  have hIq1 : ContinuousOn Iq1 (gn21Lemma5CanonicalEndpointDomain (shape 1)) := by
    dsimp [Iq1]
    exact continuousOn_setIntegral_gn21Lemma5CanonicalEndpointPolicy
      (mu 1) q1 hq1 (shape 1)
  have hIt0 : ContinuousOn It0 (gn21Lemma5CanonicalEndpointDomain (shape 0)) := by
    dsimp [It0]
    exact continuousOn_setIntegral_gn21Lemma5CanonicalEndpointPolicy
      (mu 0) (fun tau : TripLength => tau) htime0 (shape 0)
  have hIt1 : ContinuousOn It1 (gn21Lemma5CanonicalEndpointDomain (shape 1)) := by
    dsimp [It1]
    exact continuousOn_setIntegral_gn21Lemma5CanonicalEndpointPolicy
      (mu 1) (fun tau : TripLength => tau) htime1 (shape 1)
  have hIw0 : ContinuousOn Iw0 (gn21Lemma5CanonicalEndpointDomain (shape 0)) := by
    dsimp [Iw0]
    exact continuousOn_setIntegral_gn21Lemma5CanonicalEndpointPolicy
      (mu 0) (w 0) hw0 (shape 0)
  have hIw1 : ContinuousOn Iw1 (gn21Lemma5CanonicalEndpointDomain (shape 1)) := by
    dsimp [Iw1]
    exact continuousOn_setIntegral_gn21Lemma5CanonicalEndpointPolicy
      (mu 1) (w 1) hw1 (shape 1)
  let domain := gn21Lemma5CanonicalPairEndpointDomain shape
  have hIq0pair : ContinuousOn
      (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape => Iq0 endpoints.1)
      domain := by
    simpa [Function.comp_def] using
      hIq0.comp continuous_fst.continuousOn (fun endpoints hmem => hmem.1)
  have hIq1pair : ContinuousOn
      (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape => Iq1 endpoints.2)
      domain := by
    simpa [Function.comp_def] using
      hIq1.comp continuous_snd.continuousOn (fun endpoints hmem => hmem.2)
  have hIt0pair : ContinuousOn
      (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape => It0 endpoints.1)
      domain := by
    simpa [Function.comp_def] using
      hIt0.comp continuous_fst.continuousOn (fun endpoints hmem => hmem.1)
  have hIt1pair : ContinuousOn
      (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape => It1 endpoints.2)
      domain := by
    simpa [Function.comp_def] using
      hIt1.comp continuous_snd.continuousOn (fun endpoints hmem => hmem.2)
  have hIw0pair : ContinuousOn
      (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape => Iw0 endpoints.1)
      domain := by
    simpa [Function.comp_def] using
      hIw0.comp continuous_fst.continuousOn (fun endpoints hmem => hmem.1)
  have hIw1pair : ContinuousOn
      (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape => Iw1 endpoints.2)
      domain := by
    simpa [Function.comp_def] using
      hIw1.comp continuous_snd.continuousOn (fun endpoints hmem => hmem.2)
  let Q0 : GN21Lemma5CanonicalPairEndpointVector shape -> ℝ := fun endpoints =>
    gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
      (gn21EndpointVectorPolicy endpoints.1)
  let Q1 : GN21Lemma5CanonicalPairEndpointVector shape -> ℝ := fun endpoints =>
    gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
      (gn21EndpointVectorPolicy endpoints.2)
  let T0 : GN21Lemma5CanonicalPairEndpointVector shape -> ℝ := fun endpoints =>
    gn21ScaledStateTime (mu 0) (arrival 0)
      (gn21EndpointVectorPolicy endpoints.1)
  let T1 : GN21Lemma5CanonicalPairEndpointVector shape -> ℝ := fun endpoints =>
    gn21ScaledStateTime (mu 1) (arrival 1)
      (gn21EndpointVectorPolicy endpoints.2)
  let W0 : GN21Lemma5CanonicalPairEndpointVector shape -> ℝ := fun endpoints =>
    gn21ScaledStateEarning (mu 0) (arrival 0) (w 0)
      (gn21EndpointVectorPolicy endpoints.1)
  let W1 : GN21Lemma5CanonicalPairEndpointVector shape -> ℝ := fun endpoints =>
    gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
      (gn21EndpointVectorPolicy endpoints.2)
  have hQ0 : ContinuousOn Q0 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          switch12 + arrival 0 * Iq0 endpoints.1) domain :=
      continuous_const.continuousOn.add (hIq0pair.const_mul (arrival 0))
    apply hmodel.congr
    intro endpoints hmem
    rfl
  have hQ1 : ContinuousOn Q1 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          switch21 + arrival 1 * Iq1 endpoints.2) domain :=
      continuous_const.continuousOn.add (hIq1pair.const_mul (arrival 1))
    apply hmodel.congr
    intro endpoints hmem
    rfl
  have hT0 : ContinuousOn T0 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          1 + arrival 0 * It0 endpoints.1) domain :=
      continuous_const.continuousOn.add (hIt0pair.const_mul (arrival 0))
    apply hmodel.congr
    intro endpoints hmem
    rfl
  have hT1 : ContinuousOn T1 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          1 + arrival 1 * It1 endpoints.2) domain :=
      continuous_const.continuousOn.add (hIt1pair.const_mul (arrival 1))
    apply hmodel.congr
    intro endpoints hmem
    rfl
  have hW0 : ContinuousOn W0 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          arrival 0 * Iw0 endpoints.1) domain :=
      hIw0pair.const_mul (arrival 0)
    apply hmodel.congr
    intro endpoints hmem
    rfl
  have hW1 : ContinuousOn W1 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          arrival 1 * Iw1 endpoints.2) domain :=
      hIw1pair.const_mul (arrival 1)
    apply hmodel.congr
    intro endpoints hmem
    rfl
  have hnum : ContinuousOn (fun endpoints => Q0 endpoints * W1 endpoints +
      Q1 endpoints * W0 endpoints) domain :=
    (hQ0.mul hW1).add (hQ1.mul hW0)
  have hden : ContinuousOn (fun endpoints => Q0 endpoints * T1 endpoints +
      Q1 endpoints * T0 endpoints) domain :=
    (hQ0.mul hT1).add (hQ1.mul hT0)
  have hden_ne : ∀ endpoints, endpoints ∈ domain ->
      Q0 endpoints * T1 endpoints + Q1 endpoints * T0 endpoints ≠ 0 := by
    intro endpoints hmem
    have hfeasible := gn21Lemma5CanonicalPairPolicy_feasibleOpen shape endpoints
    have hQ0_pos : 0 < Q0 endpoints := by
      dsimp [Q0]
      exact gn21ExitWeightIntegral_pos_of_switch_pos
        (mu 0) (arrival 0) switch12 switch21
        (gn21EndpointVectorPolicy endpoints.1) (le_of_lt harrival0_pos)
        hswitch12_pos hsum0 (hfeasible 0).2.measurableSet (hfeasible 0).1
    have hQ1_pos : 0 < Q1 endpoints := by
      dsimp [Q1]
      exact gn21ExitWeightIntegral_pos_of_switch_pos
        (mu 1) (arrival 1) switch21 switch12
        (gn21EndpointVectorPolicy endpoints.2) (le_of_lt harrival1_pos)
        hswitch21_pos hsum1 (hfeasible 1).2.measurableSet (hfeasible 1).1
    have hT0_pos : 0 < T0 endpoints := by
      dsimp [T0]
      exact gn21ScaledStateTime_pos_of_nonneg
        (mu 0) (arrival 0) (gn21EndpointVectorPolicy endpoints.1)
        (le_of_lt harrival0_pos) (hfeasible 0).2.measurableSet (hfeasible 0).1
    have hT1_pos : 0 < T1 endpoints := by
      dsimp [T1]
      exact gn21ScaledStateTime_pos_of_nonneg
        (mu 1) (arrival 1) (gn21EndpointVectorPolicy endpoints.2)
        (le_of_lt harrival1_pos) (hfeasible 1).2.measurableSet (hfeasible 1).1
    exact (gn21AggregateDenominator_pos_of_pos
      (Q0 endpoints) (Q1 endpoints) (T0 endpoints) (T1 endpoints)
      hQ0_pos hQ1_pos hT0_pos hT1_pos).ne'
  have hquotient : ContinuousOn
      (fun endpoints =>
        (Q0 endpoints * W1 endpoints + Q1 endpoints * W0 endpoints) /
          (Q0 endpoints * T1 endpoints + Q1 endpoints * T0 endpoints)) domain :=
    hnum.div hden hden_ne
  apply hquotient.congr
  intro endpoints hmem
  change gn21MeasuredAggregateRewardPrimitives
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (gn21EndpointVectorPolicy endpoints.1)
      (gn21EndpointVectorPolicy endpoints.2) = _
  simp only [gn21MeasuredAggregateRewardPrimitives, gn21AggregateDynamicReward]
  rfl

/-- The actual aggregate reward is continuous when an arbitrary finite
positive-branch endpoint policy replaces the non-surge state of a feasible
policy.  This derives the finite-endpoint continuity used by Lemma 5 directly
from the model integrals; it is not an additional behavioral assumption. -/
theorem continuousOn_gn21AggregateDynamicRewardFunctional_update_zero_endpointPolicy
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (rho : Fin 2 -> TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho)
    (extra : Nat) :
    ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 0 (gn21EndpointVectorPolicy endpoints)))
      (gn21Lemma5EndpointDomain .positive extra) := by
  let domain := gn21Lemma5EndpointDomain .positive extra
  let q0 : TripLength -> ℝ := fun tau => gn21SwitchProb switch12 switch21 tau
  let q1 : TripLength -> ℝ := fun tau => gn21SwitchProb switch21 switch12 tau
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 : IntegrableOn q0 acceptAllPolicy (mu 0) := by
    dsimp [q0]
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 0) switch12 switch21 acceptAllPolicy (le_of_lt hswitch12_pos)
      hsum0 (fun _ h => h) measurableSet_acceptAllPolicy htime0
  have hq1 : IntegrableOn q1 acceptAllPolicy (mu 1) := by
    dsimp [q1]
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 1) switch21 switch12 acceptAllPolicy (le_of_lt hswitch21_pos)
      hsum1 (fun _ h => h) measurableSet_acceptAllPolicy htime1
  have hdomain_ordered :
      domain ⊆ gn21OrderedEndpointVectors (extra + 1) := by
    intro endpoints hdomain
    exact hdomain.1.1
  have hIq0 : ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, q0 tau ∂(mu 0)) domain := by
    exact (continuousOn_setIntegral_gn21EndpointVectorPolicy (mu 0) q0 hq0
      (extra + 1)).mono hdomain_ordered
  have hIt0 : ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, tau ∂(mu 0)) domain := by
    exact (continuousOn_setIntegral_gn21EndpointVectorPolicy (mu 0)
      (fun tau : TripLength => tau) htime0 (extra + 1)).mono hdomain_ordered
  have hIw0 : ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, w 0 tau ∂(mu 0)) domain := by
    exact (continuousOn_setIntegral_gn21EndpointVectorPolicy (mu 0) (w 0)
      hw0 (extra + 1)).mono hdomain_ordered
  let Q0 : GN21Lemma5EndpointVector extra -> ℝ := fun endpoints =>
    gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
      (gn21EndpointVectorPolicy endpoints)
  let Q1 : ℝ :=
    gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1)
  let T0 : GN21Lemma5EndpointVector extra -> ℝ := fun endpoints =>
    gn21ScaledStateTime (mu 0) (arrival 0) (gn21EndpointVectorPolicy endpoints)
  let T1 : ℝ := gn21ScaledStateTime (mu 1) (arrival 1) (rho 1)
  let W0 : GN21Lemma5EndpointVector extra -> ℝ := fun endpoints =>
    gn21ScaledStateEarning (mu 0) (arrival 0) (w 0)
      (gn21EndpointVectorPolicy endpoints)
  let W1 : ℝ := gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)
  have hQ0 : ContinuousOn Q0 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5EndpointVector extra =>
          switch12 + arrival 0 *
            ∫ tau in gn21EndpointVectorPolicy endpoints, q0 tau ∂(mu 0)) domain :=
      continuous_const.continuousOn.add (hIq0.const_mul (arrival 0))
    apply hmodel.congr
    intro endpoints _
    rfl
  have hT0 : ContinuousOn T0 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5EndpointVector extra =>
          1 + arrival 0 *
            ∫ tau in gn21EndpointVectorPolicy endpoints, tau ∂(mu 0)) domain :=
      continuous_const.continuousOn.add (hIt0.const_mul (arrival 0))
    apply hmodel.congr
    intro endpoints _
    rfl
  have hW0 : ContinuousOn W0 domain := by
    apply (hIw0.const_mul (arrival 0)).congr
    intro endpoints _
    rfl
  have hQ1_pos : 0 < Q1 := by
    dsimp [Q1]
    exact gn21ExitWeightIntegral_pos_of_switch_pos
      (mu 1) (arrival 1) switch21 switch12 (rho 1)
      (le_of_lt harrival1_pos) hswitch21_pos hsum1
      (hrho 1).2.measurableSet (hrho 1).1
  have hT1_pos : 0 < T1 := by
    dsimp [T1]
    exact gn21ScaledStateTime_pos_of_nonneg
      (mu 1) (arrival 1) (rho 1) (le_of_lt harrival1_pos)
      (hrho 1).2.measurableSet (hrho 1).1
  have hQ0_pos : ∀ endpoints ∈ domain, 0 < Q0 endpoints := by
    intro endpoints _
    dsimp [Q0]
    exact gn21ExitWeightIntegral_pos_of_switch_pos
      (mu 0) (arrival 0) switch12 switch21
      (gn21EndpointVectorPolicy endpoints) (le_of_lt harrival0_pos)
      hswitch12_pos hsum0 (gn21EndpointVectorPolicy_measurable endpoints)
      (gn21EndpointVectorPolicy_subset_acceptAll endpoints)
  have hT0_pos : ∀ endpoints ∈ domain, 0 < T0 endpoints := by
    intro endpoints _
    dsimp [T0]
    exact gn21ScaledStateTime_pos_of_nonneg
      (mu 0) (arrival 0) (gn21EndpointVectorPolicy endpoints)
      (le_of_lt harrival0_pos) (gn21EndpointVectorPolicy_measurable endpoints)
      (gn21EndpointVectorPolicy_subset_acceptAll endpoints)
  have hnum : ContinuousOn
      (fun endpoints => Q0 endpoints * W1 + Q1 * W0 endpoints) domain :=
    (hQ0.mul continuous_const.continuousOn).add
      (continuous_const.continuousOn.mul hW0)
  have hden : ContinuousOn
      (fun endpoints => Q0 endpoints * T1 + Q1 * T0 endpoints) domain :=
    (hQ0.mul continuous_const.continuousOn).add
      (continuous_const.continuousOn.mul hT0)
  have hden_ne : ∀ endpoints, endpoints ∈ domain ->
      Q0 endpoints * T1 + Q1 * T0 endpoints ≠ 0 := by
    intro endpoints hmem
    exact (gn21AggregateDenominator_pos_of_pos
      (Q0 endpoints) Q1 (T0 endpoints) T1
      (hQ0_pos endpoints hmem) hQ1_pos (hT0_pos endpoints hmem) hT1_pos).ne'
  have hquotient : ContinuousOn
      (fun endpoints =>
        (Q0 endpoints * W1 + Q1 * W0 endpoints) /
          (Q0 endpoints * T1 + Q1 * T0 endpoints)) domain :=
    hnum.div hden hden_ne
  apply hquotient.congr
  intro endpoints _
  change gn21MeasuredAggregateRewardPrimitives
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (gn21EndpointVectorPolicy endpoints) (rho 1) = _
  simp only [gn21MeasuredAggregateRewardPrimitives, gn21AggregateDynamicReward]
  rfl

/-- The actual aggregate reward is continuous when an arbitrary finite
positive-branch endpoint policy replaces the surge state of a feasible policy.
This is the state-1 counterpart of the preceding model-continuity lemma. -/
theorem continuousOn_gn21AggregateDynamicRewardFunctional_update_one_endpointPolicy
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (rho : Fin 2 -> TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho)
    (extra : Nat) :
    ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 1 (gn21EndpointVectorPolicy endpoints)))
      (gn21Lemma5EndpointDomain .positive extra) := by
  let domain := gn21Lemma5EndpointDomain .positive extra
  let q0 : TripLength -> ℝ := fun tau => gn21SwitchProb switch12 switch21 tau
  let q1 : TripLength -> ℝ := fun tau => gn21SwitchProb switch21 switch12 tau
  have hsum0 : 0 < switch12 + switch21 := add_pos hswitch12_pos hswitch21_pos
  have hsum1 : 0 < switch21 + switch12 := add_pos hswitch21_pos hswitch12_pos
  have hq0 : IntegrableOn q0 acceptAllPolicy (mu 0) := by
    dsimp [q0]
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 0) switch12 switch21 acceptAllPolicy (le_of_lt hswitch12_pos)
      hsum0 (fun _ h => h) measurableSet_acceptAllPolicy htime0
  have hq1 : IntegrableOn q1 acceptAllPolicy (mu 1) := by
    dsimp [q1]
    exact integrableOn_gn21SwitchProb_of_time_integrable
      (mu 1) switch21 switch12 acceptAllPolicy (le_of_lt hswitch21_pos)
      hsum1 (fun _ h => h) measurableSet_acceptAllPolicy htime1
  have hdomain_ordered :
      domain ⊆ gn21OrderedEndpointVectors (extra + 1) := by
    intro endpoints hdomain
    exact hdomain.1.1
  have hIq1 : ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, q1 tau ∂(mu 1)) domain := by
    exact (continuousOn_setIntegral_gn21EndpointVectorPolicy (mu 1) q1 hq1
      (extra + 1)).mono hdomain_ordered
  have hIt1 : ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, tau ∂(mu 1)) domain := by
    exact (continuousOn_setIntegral_gn21EndpointVectorPolicy (mu 1)
      (fun tau : TripLength => tau) htime1 (extra + 1)).mono hdomain_ordered
  have hIw1 : ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        ∫ tau in gn21EndpointVectorPolicy endpoints, w 1 tau ∂(mu 1)) domain := by
    exact (continuousOn_setIntegral_gn21EndpointVectorPolicy (mu 1) (w 1)
      hw1 (extra + 1)).mono hdomain_ordered
  let Q0 : ℝ :=
    gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0)
  let Q1 : GN21Lemma5EndpointVector extra -> ℝ := fun endpoints =>
    gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
      (gn21EndpointVectorPolicy endpoints)
  let T0 : ℝ := gn21ScaledStateTime (mu 0) (arrival 0) (rho 0)
  let T1 : GN21Lemma5EndpointVector extra -> ℝ := fun endpoints =>
    gn21ScaledStateTime (mu 1) (arrival 1) (gn21EndpointVectorPolicy endpoints)
  let W0 : ℝ := gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0)
  let W1 : GN21Lemma5EndpointVector extra -> ℝ := fun endpoints =>
    gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
      (gn21EndpointVectorPolicy endpoints)
  have hQ1 : ContinuousOn Q1 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5EndpointVector extra =>
          switch21 + arrival 1 *
            ∫ tau in gn21EndpointVectorPolicy endpoints, q1 tau ∂(mu 1)) domain :=
      continuous_const.continuousOn.add (hIq1.const_mul (arrival 1))
    apply hmodel.congr
    intro endpoints _
    rfl
  have hT1 : ContinuousOn T1 domain := by
    have hmodel : ContinuousOn
        (fun endpoints : GN21Lemma5EndpointVector extra =>
          1 + arrival 1 *
            ∫ tau in gn21EndpointVectorPolicy endpoints, tau ∂(mu 1)) domain :=
      continuous_const.continuousOn.add (hIt1.const_mul (arrival 1))
    apply hmodel.congr
    intro endpoints _
    rfl
  have hW1 : ContinuousOn W1 domain := by
    apply (hIw1.const_mul (arrival 1)).congr
    intro endpoints _
    rfl
  have hQ0_pos : 0 < Q0 := by
    dsimp [Q0]
    exact gn21ExitWeightIntegral_pos_of_switch_pos
      (mu 0) (arrival 0) switch12 switch21 (rho 0)
      (le_of_lt harrival0_pos) hswitch12_pos hsum0
      (hrho 0).2.measurableSet (hrho 0).1
  have hT0_pos : 0 < T0 := by
    dsimp [T0]
    exact gn21ScaledStateTime_pos_of_nonneg
      (mu 0) (arrival 0) (rho 0) (le_of_lt harrival0_pos)
      (hrho 0).2.measurableSet (hrho 0).1
  have hQ1_pos : ∀ endpoints ∈ domain, 0 < Q1 endpoints := by
    intro endpoints _
    dsimp [Q1]
    exact gn21ExitWeightIntegral_pos_of_switch_pos
      (mu 1) (arrival 1) switch21 switch12
      (gn21EndpointVectorPolicy endpoints) (le_of_lt harrival1_pos)
      hswitch21_pos hsum1 (gn21EndpointVectorPolicy_measurable endpoints)
      (gn21EndpointVectorPolicy_subset_acceptAll endpoints)
  have hT1_pos : ∀ endpoints ∈ domain, 0 < T1 endpoints := by
    intro endpoints _
    dsimp [T1]
    exact gn21ScaledStateTime_pos_of_nonneg
      (mu 1) (arrival 1) (gn21EndpointVectorPolicy endpoints)
      (le_of_lt harrival1_pos) (gn21EndpointVectorPolicy_measurable endpoints)
      (gn21EndpointVectorPolicy_subset_acceptAll endpoints)
  have hnum : ContinuousOn
      (fun endpoints => Q0 * W1 endpoints + Q1 endpoints * W0) domain :=
    (continuous_const.continuousOn.mul hW1).add
      (hQ1.mul continuous_const.continuousOn)
  have hden : ContinuousOn
      (fun endpoints => Q0 * T1 endpoints + Q1 endpoints * T0) domain :=
    (continuous_const.continuousOn.mul hT1).add
      (hQ1.mul continuous_const.continuousOn)
  have hden_ne : ∀ endpoints, endpoints ∈ domain ->
      Q0 * T1 endpoints + Q1 endpoints * T0 ≠ 0 := by
    intro endpoints hmem
    exact (gn21AggregateDenominator_pos_of_pos
      Q0 (Q1 endpoints) T0 (T1 endpoints)
      hQ0_pos (hQ1_pos endpoints hmem) hT0_pos (hT1_pos endpoints hmem)).ne'
  have hquotient : ContinuousOn
      (fun endpoints =>
        (Q0 * W1 endpoints + Q1 endpoints * W0) /
          (Q0 * T1 endpoints + Q1 endpoints * T0)) domain :=
    hnum.div hden hden_ne
  apply hquotient.congr
  intro endpoints _
  change gn21MeasuredAggregateRewardPrimitives
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (gn21EndpointVectorPolicy endpoints) = _
  simp only [gn21MeasuredAggregateRewardPrimitives, gn21AggregateDynamicReward]
  rfl

/-- Model-derived endpoint continuity for replacing either state of a feasible
two-state policy by an arbitrary finite positive-branch endpoint vector. -/
theorem continuousOn_gn21AggregateDynamicRewardFunctional_update_endpointPolicy
    (mu : Fin 2 -> Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 -> ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 -> PricingFunction)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (rho : Fin 2 -> TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho)
    (state : Fin 2) (extra : Nat) :
    ContinuousOn
      (fun endpoints : GN21Lemma5EndpointVector extra =>
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
      (gn21Lemma5EndpointDomain .positive extra) := by
  fin_cases state
  · exact continuousOn_gn21AggregateDynamicRewardFunctional_update_zero_endpointPolicy
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0 htime1 hw0 hw1 rho hrho extra
  · exact continuousOn_gn21AggregateDynamicRewardFunctional_update_one_endpointPolicy
      mu arrival switch12 switch21 w harrival0_pos harrival1_pos hswitch12_pos
      hswitch21_pos htime0 htime1 hw0 hw1 rho hrho extra

/-- Affine Appendix-D prices are integrable on the source acceptance domain
whenever trip time is integrable and the source measure is finite. -/
theorem integrableOn_affinePricing_acceptAll_of_time_integrable
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    (m a : ℝ)
    (htime : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy mu) :
    IntegrableOn (affinePricing m a) acceptAllPolicy mu := by
  unfold affinePricing
  exact (htime.const_mul m).add (integrableOn_const)

end GN21DriverSurgePricing
