import GN21DriverSurgePricing.Lemma5Variational

/-!
# Weak canonical-family attainment for GN21 Theorem 4

This is the compactness part of the Appendix-D argument, isolated from the
legacy endpoint-variation engine.  It deliberately asks only for a direct
policy-by-policy weak replacement into the explicit source canonical family.
The caller must prove that replacement from the actual aggregate objective.
-/

open AppliedModelingLib
open MeasureTheory

namespace GN21DriverSurgePricing

/--
If the actual reward is continuous on the explicit compact source-form family
and every feasible open policy is weakly dominated by a member of that family,
then an open global maximizer exists in the source family.

Unlike the older combined theorem, this result makes no endpoint derivative,
strict-improvement, optimizer-form, or source-model assumption.  It is a
plain compact-max argument.
-/
theorem exists_dynamicOpenOptimal_of_weak_canonical_dominance
    (R : DynamicReward)
    (shape : Fin 2 -> Lemma5DerivativeShape)
    (hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          R (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape))
    (hreplace :
      forall rho : Fin 2 -> TripPolicy,
        dynamicFeasibleOpenPolicy rho ->
          exists tau : Fin 2 -> TripPolicy,
            dynamicFeasibleOpenPolicy tau /\
              lemma5SourcePolicyForm (shape 0) (tau 0) /\
              lemma5SourcePolicyForm (shape 1) (tau 1) /\
              R rho <= R tau) :
    exists rho : Fin 2 -> TripPolicy,
      dynamicOpenOptimal R rho /\
        lemma5SourcePolicyForm (shape 0) (rho 0) /\
        lemma5SourcePolicyForm (shape 1) (rho 1) := by
  rcases
      (isCompact_gn21Lemma5CanonicalPairEndpointDomain shape).exists_isMaxOn
        (gn21Lemma5CanonicalPairEndpointDomain_nonempty shape)
        hpair_continuous with
    ⟨rawEndpoints, hraw_domain, hraw_max⟩
  rw [isMaxOn_iff] at hraw_max
  let rawPolicy := gn21Lemma5CanonicalPairPolicy shape rawEndpoints
  have hraw_feasible : dynamicFeasibleOpenPolicy rawPolicy :=
    gn21Lemma5CanonicalPairPolicy_feasibleOpen shape rawEndpoints
  rcases hreplace rawPolicy hraw_feasible with
    ⟨rhoStar, hrhoStar_feasible, hrhoStar_form0, hrhoStar_form1,
      hraw_le_star⟩
  rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hrhoStar_form0 with
    ⟨starEndpoints0, hstarEndpoints0, hstarPolicy0⟩
  rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hrhoStar_form1 with
    ⟨starEndpoints1, hstarEndpoints1, hstarPolicy1⟩
  let starEndpoints : GN21Lemma5CanonicalPairEndpointVector shape :=
    (starEndpoints0, starEndpoints1)
  have hstar_domain :
      starEndpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape :=
    ⟨hstarEndpoints0, hstarEndpoints1⟩
  have hstar_policy :
      gn21Lemma5CanonicalPairPolicy shape starEndpoints = rhoStar := by
    funext i
    fin_cases i
    · simpa [starEndpoints, gn21Lemma5CanonicalPairPolicy] using hstarPolicy0
    · simpa [starEndpoints, gn21Lemma5CanonicalPairPolicy] using hstarPolicy1
  have hstar_le_raw : R rhoStar <= R rawPolicy := by
    simpa [rawPolicy, hstar_policy] using hraw_max starEndpoints hstar_domain
  have hstar_eq_raw : R rhoStar = R rawPolicy :=
    le_antisymm hstar_le_raw hraw_le_star
  have hrhoStar_optimal : dynamicOpenOptimal R rhoStar := by
    refine ⟨hrhoStar_feasible, ?_⟩
    intro rho hrho
    rcases hreplace rho hrho with
      ⟨tau, htau_feasible, htau_form0, htau_form1, hrho_le_tau⟩
    rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm htau_form0 with
      ⟨tauEndpoints0, htauEndpoints0, htauPolicy0⟩
    rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm htau_form1 with
      ⟨tauEndpoints1, htauEndpoints1, htauPolicy1⟩
    let tauEndpoints : GN21Lemma5CanonicalPairEndpointVector shape :=
      (tauEndpoints0, tauEndpoints1)
    have htau_domain :
        tauEndpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape :=
      ⟨htauEndpoints0, htauEndpoints1⟩
    have htau_policy : gn21Lemma5CanonicalPairPolicy shape tauEndpoints = tau := by
      funext i
      fin_cases i
      · simpa [tauEndpoints, gn21Lemma5CanonicalPairPolicy] using htauPolicy0
      · simpa [tauEndpoints, gn21Lemma5CanonicalPairPolicy] using htauPolicy1
    have htau_le_star : R tau <= R rhoStar := by
      have htau_le_raw : R tau <= R rawPolicy := by
        simpa [rawPolicy, htau_policy] using hraw_max tauEndpoints htau_domain
      rw [hstar_eq_raw]
      exact htau_le_raw
    exact hrho_le_tau.trans htau_le_star
  exact ⟨rhoStar, hrhoStar_optimal, hrhoStar_form0, hrhoStar_form1⟩

end GN21DriverSurgePricing
