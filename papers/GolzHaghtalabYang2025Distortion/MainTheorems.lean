import AppliedModelingLib.Alignment.Welfare.Borda
import AppliedModelingLib.Alignment.Welfare.Distortion
import AppliedModelingLib.Alignment.Welfare.PopulationPreferenceGame
import AppliedModelingLib.Foundations.Probability.FiniteKLDuality
import AppliedModelingLib.GameTheory.PreferenceGame.KLDuality
import GolzHaghtalabYang2025Distortion.Theorem3
import GolzHaghtalabYang2025Distortion.Theorem3D2Source

/-!
# Finite source theorems: Gölz--Haghtalab--Yang (2025)

This module realizes the published finite-population forms of Lemma 1, the
population-limit part of Theorem 2, and the finite one-comparison-per-user
endpoint of Theorem 3 for unit-interval utility profiles. It also proves the
population-limit welfare bridge for Theorem 7 and reexports the source-facing
finite-report `d ≥ 2` endpoint from `Theorem3D2Source`.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib.Alignment.Welfare

/-- The finite realization of the source's Lemma 1 affine sandwich. -/
theorem lemma1_population_bradleyTerry_linearization_finite_core
    {User Alternative : Type} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility) {btScale : ℝ} (hbtScale : 0 < btScale)
    (first second : Alternative) :
    btScale *
          (sigmoidChordSlope btScale * populationAverageUtility population utility first -
            (1 : ℝ) / 4 * populationAverageUtility population utility second) ≤
        (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
          first second - (1 : ℝ) / 2 ∧
      (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
          first second - (1 : ℝ) / 2 ≤
        btScale *
          ((1 : ℝ) / 4 * populationAverageUtility population utility first -
            sigmoidChordSlope btScale * populationAverageUtility population utility second) :=
  populationBradleyTerryPreference_linearization_source population utility hutility hbtScale
    first second

/--
Finite population-limit specialization of source Theorem 2. Every maximizer
of the limiting Borda score has the source's squared-chord welfare factor
against every alternative. The finite-sample rate is deliberately excluded.
-/
theorem theorem2_borda_population_limit_finite_core
    {User Alternative : Type} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (winner : Alternative)
    (hmax : ∀ alternative,
      pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) alternative ≤
        pairwiseBordaScore sampling
          (populationBradleyTerryPreference population utility btScale) winner)
    (alternative : Alternative) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
        populationAverageUtility population utility alternative ≤
      populationAverageUtility population utility winner :=
  pairwiseBordaScore_welfare_lower_bound_of_maximizer population utility hutility sampling
    hbtScale winner hmax alternative

/--
Finite population-limit form of source Theorem 7. The paper's KL ball is
represented by `InFiniteKLBall`, and the hypothesis is the source's attained
constrained `argmax min` policy definition. Finite KL-ball compactness and
Sion minimax supply such a policy; the checked source bridge then supplies the
centered zero-sum inequality used in the published one-linearization proof.
-/
theorem theorem7_nlhf_population_limit_core
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (reference : PMF Alternative) (klBudget : ℝ)
    (nlhfPolicy benchmark : PMF Alternative)
    (hnlhf : IsConstrainedPopulationBradleyTerryMaximin
      population utility btScale reference klBudget nlhfPolicy)
    (hbenchmark : InFiniteKLBall reference klBudget benchmark) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark ≤
      policyAverageUtility population utility nlhfPolicy :=
  constrainedPopulationBradleyTerryEquilibrium_welfare_lower_bound_source
    population utility hutility hbtScale reference klBudget nlhfPolicy benchmark
    (contextFree_constrainedPopulationBradleyTerryMaximin_implies_populationEquilibrium
      population utility btScale reference klBudget nlhfPolicy hnlhf)
    hbenchmark

/--
Finite context-free form of source Corollary 4. An unregularized maximal
lottery has nonnegative centered margin against every alternative policy, so
Theorem 7 applies with the whole finite simplex as the feasible set.
-/
theorem corollary4_maximalLottery_population_limit_core
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (maximalLottery benchmark : PMF Alternative)
    (hmaximal : ∀ opponent,
      0 ≤ populationBradleyTerryPolicyMargin population utility btScale maximalLottery opponent) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark ≤
      policyAverageUtility population utility maximalLottery := by
  apply populationBradleyTerryMaximin_welfare_lower_bound_source
    population utility hutility hbtScale (fun _ => True) maximalLottery benchmark
  · exact ⟨trivial, fun opponent _ => hmaximal opponent⟩
  · trivial

/--
Finite population-limit form of source Corollary 8 for a finite real
regularization weight. A regularized NLHF equilibrium is constrained-optimal
at its attained KL radius, so Theorem 7 applies to every no-more-divergent
benchmark policy.
-/
theorem corollary8_regularizedNlhf_population_limit_core
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (reference policy : PMF Alternative) (klRegularization : ℝ)
    (hregularization : 0 ≤ klRegularization)
    (hequilibrium : AppliedModelingLib.GameTheory.PreferenceGame.IsRegularizedPreferenceGameEquilibrium
      (PMF.pure PUnit.unit.{1}) (populationBradleyTerryPreference population utility btScale)
      (contextFreeAlternativePolicy reference) (contextFreeAlternativePolicy policy)
      klRegularization)
    (benchmark : PMF Alternative)
    (hbenchmark : AppliedModelingLib.finiteKLDivergence benchmark reference ≤
      AppliedModelingLib.finiteKLDivergence policy reference) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark ≤
      policyAverageUtility population utility policy := by
  apply constrainedPopulationBradleyTerryEquilibrium_welfare_lower_bound_source
    population utility hutility hbtScale reference (AppliedModelingLib.finiteKLDivergence policy reference) policy benchmark
  · exact contextFree_regularizedPreferenceEquilibrium_implies_populationEquilibrium
      population utility btScale reference policy klRegularization hregularization hequilibrium
  · exact hbenchmark

/--
Finite `d = 1` endpoint of Appendix E.3's Theorem-3 argument.  It includes
the source's labelled-observation indistinguishability, its fixed-special
pigeonhole subsequence, and the exact finite welfare bound preceding Eq. (11).
-/
theorem theorem3_d1_finite_core
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (rule : ∀ horizon,
      (Fin horizon → ((Alternative × Alternative) × Bool)) → PMF Alternative) :
    ∃ special : Alternative,
      Set.Infinite {horizon : ℕ |
        let policy := theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
            special horizon)
          (rule horizon)
        (policy special).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹ ∧
          policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
            (theorem3ManyAlternativeUtility epsilon 1 special) policy ≤
              (Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
                epsilon * theorem3OrdinaryTypeMass beta epsilon} :=
  theorem3_finite_d1_welfare_lower_bound_core
    pairSampling beta epsilon hbeta hepsilon rule

/--
Finite distortion form of source Theorem 3 for `d = 1`.  On the source range
`0 < epsilon ≤ 1 / 2` and with at least two alternatives, the hidden special
alternative is welfare-maximizing and the rule incurs the exact Eq. (11)
ratio along an infinite sequence of sample horizons.
-/
theorem theorem3_d1_finite_distortion_core
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (hcard : 2 ≤ Fintype.card Alternative)
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_upper : epsilon ≤ (1 : ℝ) / 2)
    (rule : ∀ horizon,
      (Fin horizon → ((Alternative × Alternative) × Bool)) → PMF Alternative) :
    ∃ special : Alternative,
      Set.Infinite {horizon : ℕ |
        let policy := theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
            special horizon)
          (rule horizon)
        (∀ alternative,
          populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
            (theorem3ManyAlternativeUtility epsilon 1 special) alternative ≤
            populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
              (theorem3ManyAlternativeUtility epsilon 1 special) special) ∧
          theorem3SpecialTypeMass beta epsilon /
              ((Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
                epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
            theorem3SpecialTypeMass beta epsilon /
              policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
                (theorem3ManyAlternativeUtility epsilon 1 special) policy} :=
  theorem3_finite_d1_distortion_lower_bound_core hcard pairSampling beta epsilon hbeta hepsilon
    hepsilon_upper rule

end GolzHaghtalabYang2025Distortion
